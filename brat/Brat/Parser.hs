module Brat.Parser (parseFile) where

import Brat.Constructors.Patterns
import Brat.Error
import Brat.FC
import Brat.Lexer (lex)
import Brat.Lexer.Bracketed (BToken(..), brackets)
import Brat.Lexer.Token (Keyword(..), Token(..), Tok(..))
import qualified Brat.Lexer.Token as Lexer
import Brat.QualName ( plain, QualName(..) )
import Brat.Syntax.Abstractor hiding (PNone)
import Brat.Syntax.CircuitProperties (CircuitProperties(..))
import Brat.Syntax.Common hiding (PNone, end)
import qualified Brat.Syntax.Common as Syntax
import Brat.Syntax.FuncDecl (FuncDecl(..), Locality(..))
import Brat.Syntax.Concrete
import Brat.Syntax.Raw
import Brat.Syntax.Simple
import Brat.Elaborator
import Data.Bracket
import Util ((**^))

import Control.Monad (void)
import Control.Monad.State (State, evalState, runState, get, put)
import Data.Bifunctor
import Data.Foldable (msum)
import Data.Functor (($>), (<&>))
import Data.List (intercalate, uncons)
import Data.List.HT (chop, viewR)
import Data.List.NonEmpty (toList, NonEmpty(..), nonEmpty)
import qualified Data.List.NonEmpty as NE
import Data.Maybe (fromJust, isJust, fromMaybe, maybeToList)
import Data.Set (empty)
import Prelude hiding (lex, round)
import Text.Megaparsec hiding (Pos, Token, State, empty, match, ParseError, parse)
import qualified Text.Megaparsec as M (parse)

newtype CustomError = Custom String deriving (Eq, Ord)

-- the State is the (FC) Position of the last token *consumed*
type Parser a = ParsecT CustomError [BToken] (State Pos) a

parse :: Parser a -> String -> [BToken] -> Either (ParseErrorBundle [BToken] CustomError) a
parse p s tks = evalState (runParserT p s tks) (Pos 0 0)

instance ShowErrorComponent CustomError where
  showErrorComponent (Custom s) = s

matchFC :: Tok -> Parser (WC ())
matchFC tok = label (show tok) $ matchTok f
 where
  f :: Tok -> Maybe ()
  f t | t == tok = Just ()
      | otherwise = Nothing

match :: Tok -> Parser ()
match = fmap unWC . matchFC

matchTok :: (Tok -> Maybe a) -> Parser (WC a)
matchTok f = token (matcher f) empty
 where
  matcher :: (Tok -> Maybe a) -> BToken -> Maybe (WC a)
  matcher f (FlatTok (Token fc t)) = WC fc <$> f t
  -- Returns the FC at the beginning of the token
  matcher f (Bracketed _ Paren [t]) = matcher f t
  matcher _ _ = Nothing

kmatch :: Keyword -> Parser (WC ())
kmatch = matchFC . K

matchString :: String -> Parser (WC ())
matchString s = label (show s) $ matchTok $ \case
  Ident ident | ident == s -> Just ()
  _ -> Nothing

hole :: Parser (WC String)
hole = label "hole" $ matchTok $ \case
  Hole h -> Just h
  _ -> Nothing

simpleName :: Parser (WC String)
simpleName = matchTok $ \case
  Ident str -> Just str
  _ -> Nothing

qualName :: Parser (WC QualName)
qualName = label "qualified name" $ matchTok $ \case
  QualifiedId prefix str -> Just (PrefixName (toList prefix) str)
  Ident str -> Just (PrefixName [] str)
  _ -> Nothing

inBrackets :: BracketType -> Parser a -> Parser a
inBrackets b p = unWC <$> inBracketsFC b p

inBracketsFC :: BracketType -> Parser a -> Parser (WC a)
inBracketsFC b p = contents >>= \(outerFC, toks) -> either (customFailure . Custom . errorBundlePretty) (pure . WC outerFC) (parse (p <* eof) "" toks)
 where
  contents = flip token empty $ \case
    Bracketed fc b' xs | b == b' -> Just (fc, xs)
    _ -> Nothing

number :: Parser (WC Int)
number = label "nat" $ matchTok $ \case
  Number n -> Just n
  _ -> Nothing

float :: Parser (WC Double)
float = label "float" $ matchTok $ \case
  FloatLit x -> Just x
  _ -> Nothing

comment :: Parser (WC ())
comment = label "Comment" $ matchTok $ \case
  Comment _ -> Just ()
  _ -> Nothing

string :: Parser (WC String)
string = matchTok $ \case
  Quoted txt -> Just txt
  _ -> Nothing

var :: Parser (WC Flat)
var = fmap FVar <$> qualName

port :: Parser (WC String)
port = simpleName

comma :: Parser (WC Flat -> WC Flat -> WC Flat)
comma = fmap unWC . matchTok $ \case
  Comma -> Just $ \a b ->
    WC (spanFCOf a b) (FJuxt a b)
  _ -> Nothing

arith :: ArithOp -> Parser (WC Flat -> WC Flat -> WC Flat)
arith op = fmap unWC . matchTok $ \tok -> case (op, tok) of
  (Add, Plus) -> Just make
  (Sub, Minus) -> Just make
  (Mul, Asterisk) -> Just make
  (Div, Slash) -> Just make
  (Pow, Caret) -> Just make
  _ -> Nothing
 where
  make a b = WC (FC (start (fcOf a)) (end (fcOf b))) (FArith op a b)

chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 px pf = px >>= rest
 where
  rhs = do f <- pf
           x <- px
           pure (f, x)

  rest x = optional rhs >>= \case
    Just (f, y) -> rest (f x y)
    Nothing     -> pure x

abstractor :: Parser (WC Abstractor)
abstractor = do ps <- many (try portPull)
                abs <- try (inBrackets Paren binders) <|> binders
                pure $ if null ps
                       then abs
                       else let fc = spanFCOf (head ps) abs in WC fc (APull (unWC <$> ps) (unWC abs))
 where
  -- Minus port pulling
  binders = try (joinBinders <$> ((:|) <$> binding <*> many (match Comma *> binding)))
   where
    joinBinders xs = let (abs, startFC, endFC) = joinBindersAux xs in WC (spanFC startFC endFC) abs

    joinBindersAux (WC fc x :| []) = (x, fc, fc)
    joinBindersAux (WC fc x :| (y:ys)) = let (abs, _, endFC) = joinBindersAux (y :| ys) in
                                           (x :||: abs, fc, endFC)

  binding :: Parser (WC Abstractor)
  binding = try (fmap APat <$> bigPat) <|> inBrackets Paren abstractor

  vecPat :: Parser (WC Pattern)
  vecPat = do
    WC fc elems <- inBracketsFC Square ((unWC <$> binding) `sepBy` match Comma)
    WC fc <$> list2Cons elems

  list2Cons :: [Abstractor] -> Parser Pattern
  list2Cons [] = pure PNil
  list2Cons (APat x:xs) = PCons x <$> list2Cons xs
  list2Cons _ = customFailure (Custom "Internal error list2Cons")

  portPull = port <* match PortColon

  -- For simplicity, we can say for now that all of our infix vector patterns have
  -- the same precedence and associate to the right
  bigPat :: Parser (WC Pattern)
  bigPat = do
    WC lfc lhs <- weePat
    rest <- optional $
            PCons lhs <$ match Cons
            <|> PSnoc lhs <$ match Snoc
            <|> PConcatEqEven lhs <$ match ConcatEqEven
            <|> PConcatEqOdd lhs <$ match ConcatEqOddL <*> (unWC <$> weePat) <* match ConcatEqOddR
            <|> PRiffle lhs <$ match Riffle
    case rest of
      Just f -> do
        WC rfc rhs <- bigPat
        pure $ WC (spanFC lfc rfc) (f rhs)
      Nothing -> pure (WC lfc lhs)


  weePat :: Parser (WC Pattern)
  weePat = try vecPat
    <|> (fmap (const DontCare) <$> matchFC Underscore)
    <|> try (fmap Lit <$> simpleTerm)
    <|> try constructorsWithArgs
    <|> try nullaryConstructors
    <|> (fmap Bind <$> simpleName)
    <|> inBrackets Paren bigPat
   where
    nullaryConstructor c = do
      WC fc () <- matchString c
      pure $ WC fc (PCon (plain c) AEmpty)

    nullaryConstructors = msum (try . nullaryConstructor <$> ["zero", "nil", "none", "true", "false"])

    constructorWithArgs :: String -> Parser (WC Pattern)
    constructorWithArgs c = do
      str <- matchString c
      abs <- inBracketsFC Paren (unWC <$> abstractor)
      pure $ WC (spanFCOf str abs) (PCon (plain c) (unWC abs))

    constructorsWithArgs = msum (try . constructorWithArgs <$> ["succ", "doub", "cons", "some"])

simpleTerm :: Parser (WC SimpleTerm)
simpleTerm =
  (fmap Text <$> string <?> "string")
  <|> try (maybeNegative Float float <?> "float")
  <|> maybeNegative Num number <?> "nat"

 where
  maybeNegative :: Num a => (a -> SimpleTerm) -> Parser (WC a)
                -> Parser (WC SimpleTerm)
  maybeNegative f p = do
    minusFC <- fmap fcOf <$> optional (matchFC Minus)
    WC nFC n <- p
    pure $ case minusFC of
      Nothing -> WC nFC (f n)
      Just minusFC -> WC (spanFC minusFC nFC) (f (negate n))

typekind :: Parser (WC TypeKind)
typekind = try (fmap (const Nat) <$> matchFC Hash) <|> kindHelper Lexer.Dollar Syntax.Dollar <|> kindHelper Asterisk Star
 where
  kindHelper tok con  = do
    WC conFC () <- matchFC tok
    margs <- optional (inBracketsFC Paren row)
    let (fc, args) = maybe
                     (conFC, [])
                     (\(WC argsFC args) -> (FC (start conFC) (end argsFC), args))
                     margs
    pure $ WC fc (con args)


  row :: Parser [(PortName, TypeKind)]
  row = (`sepBy` match Comma) $ do
    p <- unWC <$> port
    match TypeColon
    (p,) . unWC <$> typekind

vtype :: Parser (WC (Raw Chk Noun))
vtype = cnoun (expr' PApp)

-- Parse a row of type and kind parameters
-- N.B. kinds must be named
-- TODO: Update definitions so we can retain the FC info, instead of forgetting it
rawIOFC :: Parser (TypeRow (WC (KindOr RawVType)))
rawIOFC = rowElem `sepBy` void (try comma)
 where
  rowElem :: Parser (TypeRowElem (WC (KindOr RawVType)))
  rowElem = try (inBrackets Paren rowElem') <|> rowElem'

  rowElem' :: Parser (TypeRowElem (WC (KindOr RawVType)))
  rowElem' = try namedKind <|> try namedType <|> ((\(WC tyFC ty) -> Anon (WC tyFC (Right ty))) <$> vtype)

  namedType :: Parser (TypeRowElem (WC (KindOr RawVType)))
  namedType = do
    WC pFC p <- port
    match TypeColon
    WC tyFC ty <- vtype
    pure (Named p (WC (spanFC pFC tyFC) (Right ty)))

  namedKind :: Parser (TypeRowElem (WC (KindOr ty)))
  namedKind = do
    WC pFC p <- port
    match TypeColon
    WC kFC k <- typekind
    pure (Named p (WC (spanFC pFC kFC) (Left k)))

rawIO :: Parser [RawIO]
rawIO = fmap (fmap unWC) <$> rawIOFC

rawIO' :: Parser ty -> Parser (TypeRow ty)
rawIO' tyP = rowElem `sepBy` void (try comma)
 where
  rowElem = try (inBrackets Paren rowElem') <|> rowElem'

  -- Look out if we can find ::. If not, backtrack and just do tyP.
  -- For example, if we get an invalid primitive type (e.g. `Int` in
  -- a kernel or a misspelled type like `Intt`), we get the better
  -- error message from tyP instead of complaining about a missing ::
  -- (since the invalid type can be parsed as a port name)
  rowElem' = optional (try $ port <* match TypeColon) >>= \case
       Just (WC _ p) -> Named p <$> tyP
       Nothing -> Anon <$> tyP

functionType :: Parser RawVType
functionType = try ctype <|> kernel
 where
  ctype = do
    ins <- inBrackets Paren $ rawIO
    match Arrow
    outs <- rawIO
    pure (RFn (ins :-> outs))

  kernel = do
    ins <- inBrackets Paren $ rawIO' (unWC <$> vtype)
    match Lolly
    isWeird <- isJust <$> optional (match Hash)
    outs <- rawIO' (unWC <$> vtype)
    pure (RKernel (if isWeird then PNone else PControllable) (ins :-> outs))

spanningFC :: TypeRow (WC ty) -> Parser (WC (TypeRow ty))
spanningFC [] = customFailure (Custom "Internal: RawIO shouldn't be empty")
spanningFC [x] = pure (WC (fcOf $ forgetPortName x) [unWC <$> x])
spanningFC (x:xs) = pure (WC (spanFC (fcOf $ forgetPortName x) (fcOf . forgetPortName $ last xs)) (fmap unWC <$> (x:xs)))

rawIOWithSpanFC :: Parser (WC [RawIO])
rawIOWithSpanFC = spanningFC =<< rawIOFC

vec :: Parser (WC Flat)
vec = (\(WC fc x) -> WC fc (unWC (vec2Cons fc x))) <$> inBracketsFC Square elems
  where
    elems = (element `chainl1` try vecComma) <|> pure []
    vecComma = match Comma $> (++)

    element :: Parser [WC Flat]
    element = (:[]) <$> expr' (succ PJuxtPull)

    mkNil fc = FCon (plain "nil") (WC fc FEmpty)

    vec2Cons :: FC -> [WC Flat] -> WC Flat
    -- The nil element gets the FC of the `[]` expression.
    -- N.B. this is also true in non-nil lists: the `nil` terminator of the list
    -- `[1,2,3]` gets the file context of `[1,2,3]`
    vec2Cons outerFC [] = WC outerFC (mkNil outerFC)
    vec2Cons outerFC [x] = WC (fcOf x) $ FCon (plain "cons") (WC (fcOf x) (FJuxt x (WC outerFC (mkNil outerFC))))
    -- We give each cell of the list an FC which starts with the FC
    -- of its head element and ends at the end of the list (the closing ']')
    vec2Cons outerFC (x:xs) = let endFC = fcOf (last xs)
                                  fc = spanFC (fcOf x) endFC
                              in WC fc $
                                 FCon (plain "cons") (WC fc (FJuxt x (vec2Cons outerFC xs)))


cthunk :: Parser (WC Flat)
cthunk = try bratFn <|> try kernel <|> thunk
 where
  bratFn = inBracketsFC Brace $ do
    ss <- rawIO
    match Arrow
    ts <- rawIO
    pure $ FFn (ss :-> ts)

  kernel = inBracketsFC Brace $ do
    ss <- rawIO' (unWC <$> vtype)
    match Lolly
    isWeird <- isJust <$> optional (match Hash)
    ts <- rawIO' (unWC <$> vtype)
    pure (FKernel (if isWeird then PNone else PControllable) (ss :-> ts))


  -- Explicit lambda or brace section
  thunk :: Parser (WC Flat)
  thunk = do
    WC bracesFC th <- inBracketsFC Brace braceSection
    pure (WC bracesFC (FThunk th))

  braceSection :: Parser (WC Flat)
  braceSection = do
    e <- expr
    -- Replace underscores with invented variable names '1, '2, '3 ...
    -- which are illegal for the user to use as variables
    case runState (replaceU e) 0 of
      (e', 0) -> pure e'
      -- If we don't have a `=>` at the start of a kernel, it could (and should)
      -- be a verb, not the RHS of a no-arg lambda
      (e', n) -> let abs = braceSectionAbstractor [0..n-1]
                 in pure $ WC (fcOf e) $ FLambda ((WC (fcOf e) abs, e') :| [])

  replaceU :: WC Flat -> State Int (WC Flat)
  replaceU (WC fc x) = WC fc <$> replaceU' x

  replaceU' :: Flat -> State Int Flat
  replaceU' FUnderscore = do
    n <- get
    put (n+1)
    pure $ FVar (PrefixName [] ('\'':show n))
  replaceU' (FThunk a) = pure $ FThunk a  -- Don't recurse into thunks!
  replaceU' (FApp a b) = FApp <$> replaceU a <*> replaceU b
  replaceU' (FJuxt a b) = FJuxt <$> replaceU a <*> replaceU b
  replaceU' (FCompose a b) = FCompose <$> replaceU a <*> replaceU b
  replaceU' (FInto a b) = FInto <$> replaceU a <*> replaceU b
  replaceU' (FLetIn abs a b) = FLetIn abs <$> replaceU a <*> replaceU b
  replaceU' (FLambda lclauses) = FLambda <$> traverse (id **^ replaceU) lclauses
  replaceU' (FAnnotation a t) = (`FAnnotation` t) <$> replaceU a
  replaceU' (FCon x a) = FCon x <$> replaceU a
  replaceU' (FPull ps a) = FPull ps <$> replaceU a
  replaceU' x = pure x

  braceSectionAbstractor :: [Int] -> Abstractor
  braceSectionAbstractor ns = foldr (:||:) AEmpty $
                              (\x -> APat (Bind ('\'': show x))) <$> ns


-- Expressions that can occur inside juxtapositions and vectors (i.e. everything with a higher
-- precedence than juxtaposition). Precedence table (loosest to tightest binding):
atomExpr :: Parser (WC Flat)
atomExpr = simpleExpr <|> inBracketsFC Paren (unWC <$> expr)
 where
  simpleExpr :: Parser (WC Flat)
  simpleExpr = fmap FHole <$> hole
            <|> try (fmap FSimple <$> simpleTerm)
            <|> try fanin
            <|> try fanout
            <|> vec
            <|> cthunk
            <|> fmap (const FPass) <$> matchFC DotDot
            <|> var
            <|> fmap (const FUnderscore) <$> matchFC Underscore
            <|> fmap (const FIdentity) <$> matchFC Pipe
            <|> fmap (const FHope) <$> matchFC Bang


{- Infix operator precedence table (See Brat.Syntax.Common.Precedence)
(loosest to tightest binding):
   =>
   |> (left-assoc)
   ;  (left-assoc)
   , & port-pull
   -, ,- =,= =,_,= =%=  (vector builders) (all right-assoc (for now!) and same precedence)
   _of_ (right-assoc)
   + -  (left-assoc)
   * /  (left-assoc)
   ^    (left-assoc)
   ::   (no associativity, i.e. explicit parenthesis required for chaining)
   app  (left-assoc)
-}
expr = expr' minBound

expr' :: Precedence -> Parser (WC Flat)
expr' p = choice $ (try . getParser <$> enumFrom p) ++ [atomExpr]
 where
  getParser :: Precedence -> Parser (WC Flat)
  getParser = \case
    PLetIn -> letIn <?> "let ... in"
    PLambda -> lambda <?> "lambda"
    PInto -> (emptyInto <|> into) <?> "into"
    PComp -> composition <?> "composition"
    PJuxtPull -> pullAndJuxt <?> "juxtaposition"
    PVecPat -> vectorBuild <?> "vector pattern"
    POf -> ofExpr <?> "vectorisation"
    PAddSub -> addSub <?> "addition or subtraction"
    PMulDiv -> mulDiv <?> "multiplication or division"
    PPow -> pow <?> "power"
    PAnn -> annotation <?> "type annotation"
    PApp -> application <?> "application"

  -- Take the precedence level and return a parser for everything with a higher precedence
  subExpr :: Precedence -> Parser (WC Flat)
  subExpr PApp = atomExpr
  subExpr p = choice $ (try . getParser <$> enumFrom (succ p)) ++ [atomExpr]

  -- Top level parser, looks for vector constructors with `atomExpr'`s as their
  -- elements.
  vectorBuild :: Parser (WC Flat)
  vectorBuild = do
    lhs <- subExpr PVecPat
    rest <- optional $
            (CCons, [lhs]) <$ match Cons
            <|> (CSnoc, [lhs]) <$ match Snoc
            <|> (CConcatEqEven, [lhs]) <$ match ConcatEqEven
            <|> (CConcatEqOdd,) . ([lhs] ++) . (:[]) <$ match ConcatEqOddL <*> subExpr (succ PVecPat) <* match ConcatEqOddR
            <|> (CRiffle, [lhs]) <$ matchFC Riffle
    case rest of
      Just (c, args) -> do
        rhs <- vectorBuild
        let juxtElems = case args of
              [] -> rhs :| []
              (a:as) -> a :| (as ++ [rhs])
        pure (WC (spanFCOf lhs rhs) (FCon c (mkJuxt juxtElems)))
      Nothing -> pure lhs

  ofExpr :: Parser (WC Flat)
  ofExpr = do
    lhs <- subExpr POf
    optional (kmatch KOf) >>= \case
      Nothing -> pure lhs
      Just _ -> do
        rhs <- ofExpr
        pure (WC (spanFCOf lhs rhs) (lhs `FOf` rhs))

  mkJuxt :: NonEmpty (WC Flat) -> WC Flat
  mkJuxt (x :| []) = x
  mkJuxt (x :| (y:ys)) = let rest = mkJuxt (y:|ys) in WC (FC (start (fcOf x)) (end (fcOf rest))) (FJuxt x rest)

  application :: Parser (WC Flat)
  application = atomExpr >>= applied
   where
    applied :: WC Flat -> Parser (WC Flat)
    applied f = do
      first <- inBracketsFC Paren $ (unWC <$> expr) <|> pure FEmpty
      let one = WC (spanFCOf f first) (FApp f first)
      optional (applied one) <&> fromMaybe one

  binary :: [ArithOp] -> Precedence -> Parser (WC Flat)
  binary ops lvl = subExpr lvl `chainl1` choice (try . arith <$> ops)

  addSub = binary [Add, Sub] PAddSub
  mulDiv = binary [Mul, Div] PMulDiv
  pow = binary [Pow] PPow

  annotation :: Parser (WC Flat)
  annotation = do
    tm <- subExpr PAnn
    colon <- matchFC TypeColon
    WC (spanFCOf tm colon) . FAnnotation tm <$> rawIO

  letIn :: Parser (WC Flat)
  letIn = label "let ... in" $ do
    let_ <- kmatch KLet
    (lhs, rhs) <- letInBinding
    kmatch KIn
    body <- expr
    pure (WC (spanFCOf let_ body) (FLetIn lhs rhs body))
   where
    letInBinding = do
      abs <- abstractor
      match Equal
      thing <- expr
      pure (abs, thing)

  -- Sequence of `abstractor => expr` separated by `|`
  lambda :: Parser (WC Flat)
  lambda = do
    firstClause <- lambdaClause
    otherClauses <- many (match Pipe >> lambdaClause)
    let endPos = case otherClauses of
          [] -> end (fcOf (snd firstClause))
          _ -> end (fcOf (snd (last otherClauses)))
    let fc = FC (start (fcOf (fst firstClause))) endPos
    pure (WC fc (FLambda (firstClause :| otherClauses)))

  -- A single `abstractor => expr`
  lambdaClause :: Parser (WC Abstractor, WC Flat)
  lambdaClause = do
    mabs <- try (Right <$> abstractor) <|> pure (Left AEmpty)
    WC arrowFC () <- matchFC FatArrow
    let abs = either (WC arrowFC) id mabs
    body <- expr
    pure (abs, body)

  emptyInto :: Parser (WC Flat)
  emptyInto = do
    -- It's tricky to come up with an FC for empty syntax
    WC lhs () <- matchFC Into
    rhs <- subExpr (pred PInto)
    pure $ WC (spanFC lhs (fcOf rhs)) $ FInto (WC lhs FEmpty) rhs

  into :: Parser (WC Flat)
  into = subExpr PInto `chainl1` divider Into FInto

  composition :: Parser (WC Flat)
  composition = subExpr PComp `chainl1` divider Semicolon FCompose

  divider :: Tok -> (WC Flat -> WC Flat -> Flat) -> Parser (WC Flat -> WC Flat -> WC Flat)
  divider tok f = fmap unWC . matchTok $ \case
    t | t == tok -> Just $ \a b ->
      WC (spanFCOf a b) (f a b)
    _ -> Nothing

  pullAndJuxt = do
    ports <- many (try portPull)
    let firstPortFC = fcOf . fst <$> uncons ports
    case ports of
      [] -> juxtRhsWithPull
      _ -> (\juxt@(WC juxtFC _) -> WC (maybe juxtFC (`spanFC` juxtFC) firstPortFC) (FPull (unWC <$> ports) juxt)) <$> juxtRhsWithPull
   where
    portPull :: Parser (WC String)
    portPull = do
      WC portFC portName <- port
      WC colonFC _ <- matchFC PortColon
      pure (WC (spanFC portFC colonFC) portName)

    -- Juxtaposition here includes port pulling, since they have the same precedence
    juxtRhsWithPull = do
      expr <- subExpr PJuxtPull
      rest <- optional (match Comma *> pullAndJuxt)
      pure $ case rest of
        Nothing -> expr
        Just rest@(WC restFC _) -> WC (spanFC (fcOf expr) restFC) (FJuxt expr rest)

fanout = inBracketsFC Square (FFanOut <$ match Slash <* match Backslash)
fanin = inBracketsFC Square (FFanIn <$ match Backslash <* match Slash)

cnoun :: Parser (WC Flat) -> Parser (WC (Raw 'Chk 'Noun))
cnoun pe = do
  e <- pe
  case elaborate e of
    Left err -> fail (showError err)
    Right (SomeRaw r) -> case do
      r <- assertChk r
      assertNoun r
     of
      Left err -> fail (showError err)
      Right r -> pure r


decl :: Parser FDecl
decl = do
      (fc, nm, ty, body) <- do
        WC startFC nm <- simpleName
        WC _ ty <- declSignature
        let allow_clauses = case ty of
                                 [Named _ (Right t)] -> is_fun_ty t
                                 [Anon (Right t)] -> is_fun_ty t
                                 _ -> False
        WC endFC body <- if allow_clauses
                         then declClauses nm <|> declNounBody nm
                         else declNounBody nm
        pure (spanFC startFC endFC, nm, ty, body)
      pure $ FuncDecl
        { fnName = nm
        , fnLoc  = fc
        , fnSig  = ty
        , fnBody = body
        , fnLocality = Local
        }
    where
      is_fun_ty :: RawVType -> Bool
      is_fun_ty (RFn _) = True
      is_fun_ty (RKernel _ _) = True
      is_fun_ty _ = False

      declClauses :: String -> Parser (WC FBody)
      declClauses nm = do
        cs <- clauses nm
        let startFC = fcOf . fst $ NE.head cs
        let endFC = fcOf . snd $ NE.last cs
        pure (WC (spanFC startFC endFC) (FClauses cs))

      declNounBody :: String -> Parser (WC FBody)
      declNounBody nm = do
        label (nm ++ "(...) = ...") $
          matchString nm
        match Equal
        body@(WC fc _) <- expr
        pure (WC fc (FNoLhs body))

class FCStream a where
  getFC :: Int -> PosState a -> FC

spToFC :: SourcePos -> FC
spToFC (SourcePos _ line col) = let
  l = unPos line
  c = unPos col
 in FC (Pos l c) (Pos l (c + 1))

instance FCStream String where
  getFC os pst = let (_, pst') = reachOffset os pst in spToFC $ pstateSourcePos pst'

instance FCStream [Token] where
  getFC o PosState{..} = case drop (o - pstateOffset) pstateInput of
    [] -> spToFC pstateSourcePos
    (Token fc _):_ -> fc

instance FCStream [BToken] where
  getFC o PosState{..} = case drop (o - pstateOffset) pstateInput of
    [] -> spToFC pstateSourcePos
    (Bracketed fc _ _):_ -> fc
    (FlatTok (Token fc _)):_ -> fc


parseFile :: String -> String -> Either SrcErr ([Import], FEnv)
parseFile fname contents = addSrcContext fname contents $ do
  toks <- first (wrapParseErr LexErr) (M.parse lex fname contents)
  btoks <- brackets toks
  first (wrapParseErr ParseErr) (parse pfile fname btoks)
 where
  wrapParseErr :: (VisualStream t, FCStream t, ShowErrorComponent e)
               => (ParseError -> ErrorMsg) -> ParseErrorBundle t e -> Error
  wrapParseErr wrapper er = let
      -- TODO: return all of the errors? There is generally only one.
      e :| errs = bundleErrors er
      prettyErr = parseErrorTextPretty e ++ case errs of
        [] -> ""
        xs -> " and " ++ show (length xs) ++ " other errors"
      fc = getFC (errorOffset e) (bundlePosState er)
    in  Err (Just fc) $ wrapper (PE prettyErr)

clauses :: String -> Parser (NonEmpty (WC Abstractor, WC Flat))
clauses declName = label "clauses" (fromJust . nonEmpty <$> some (try branch))
 where
  branch :: Parser (WC Abstractor, WC Flat)
  branch = do
    label (declName ++ "(...) = ...") $
      matchString declName
    lhs <- inBrackets Paren (abstractor <?> "binder")
    match Equal
    rhs <- expr
    pure (lhs,rhs)

pimport :: Parser Import
pimport = do
  o <- open
  kmatch KImport
  x <- qualName
  a <- alias
  Import x (not o) a <$> selection
 where
  open :: Parser Bool
  open = optional (matchString "open") >>= \case
     Nothing -> pure False
     Just _ -> pure True

  alias :: Parser (Maybe (WC String))
  alias = optional (matchString "as") >>= \case
     Nothing -> pure Nothing
     Just _ -> Just <$> simpleName

  selection :: Parser ImportSelection
  selection = optional (try $ matchString "hiding") >>= \case
    Just _ -> ImportHiding <$> list
    Nothing -> optional list >>= \case
       Nothing -> pure ImportAll
       Just ss -> pure (ImportPartial ss)

  list :: Parser [WC String]
  list = inBrackets Paren $ ((:[]) <$> simpleName) `chainl1` try (match Comma $> (++))

pstmt :: Parser FEnv
pstmt = ((comment <?> "comment")                 <&> \_ -> ([] , []))
        <|> try ((alias <?> "type alias")        <&> \x -> ([] , [x]))
        <|> try (extDecl                         <&> \x -> ([x], []))
        <|> ((decl <?> "declaration")            <&> \x -> ([x], []))
 where
  alias :: Parser RawAlias
  alias = aliasContents <&>
          \(fc, name, args, ty) -> TypeAlias fc name args ty

  aliasContents :: Parser (FC, QualName, [(String, TypeKind)], RawVType)
  aliasContents = do
    WC startFC () <- matchFC (K KType)
    WC _ alias <- qualName
    args <- option [] $ inBrackets Paren $ (unWC <$> simpleName) `sepBy` match Comma
{- future stuff
    args <- option [] $ inBrackets Paren $ (`sepBy` (match Comma)) $ do
      port <- port
      match TypeColon
      (port,) <$> typekind
-}
    match Equal
    ty <- vtype
    -- TODO: Right now we restrict the variables in a type alias to being of
    -- kind `Star []` (i.e. the type of simple types). In future we should allow
    -- users to specify the kinds of variables in type aliases, like:
    --   type X(a :: *, b :: #, c :: *(x :: *, y :: #)) = ...
    -- See KARL-325
    pure (spanFC startFC (fcOf ty), alias, (,Star []) <$> args, unWC ty)

  extDecl :: Parser FDecl
  extDecl = do (fc, fnName, ty, symbol) <- do
                  WC startFC () <- matchFC (K KExt)
                  symbol <- unWC <$> string
                  fnName <- unWC <$> simpleName
                  WC tyFC ty <- declSignature
                  -- When external ops are used, we expect it to be in the form:
                  -- extension.op for the hugr extension used and the op name
                  let bits = chop (=='.') symbol
                  (ext, op) <- case viewR bits of
                                 Just (ext, op) -> pure (intercalate "." ext, op)
                                 Nothing -> fail $ "Malformed op name: " ++ symbol
                  pure (spanFC startFC tyFC, fnName, ty, (ext, op))
               pure FuncDecl
                 { fnName = fnName
                 , fnSig = ty
                 , fnBody = FUndefined
                 , fnLoc = fc
                 , fnLocality = Extern symbol
                 }

declSignature :: Parser (WC [RawIO])
declSignature = try nDecl <|> vDecl where
 nDecl = match TypeColon >> rawIOWithSpanFC
 vDecl = functionSignature <&> fmap (\ty -> [Named "thunk" (Right ty)])

 functionSignature :: Parser (WC RawVType)
 functionSignature = try (fmap RFn <$> ctype) <|> (fmap (RKernel _) <$> kernel)
  where
   ctype :: Parser (WC RawCType)
   ctype = do
     WC startFC ins <- inBracketsFC Paren rawIO
     match Arrow
     WC endFC outs <- rawIOWithSpanFC
     pure (WC (spanFC startFC endFC) (ins :-> outs))

   kernel :: Parser (WC RawKType)
   kernel = do
     WC startFC ins <- inBracketsFC Paren $ rawIO' (unWC <$> vtype)
     match Lolly
     WC endFC outs <- spanningFC =<< rawIO' vtype
     pure (WC (spanFC startFC endFC) (ins :-> outs))




pfile :: Parser ([Import], FEnv)
pfile = do
  imports <- many pimport
  env     <- foldr (<>) ([], []) <$> (pstmt `manyTill` eof)
  pure (imports, env)
