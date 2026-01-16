#!/bin/bash

set -u

if ! which hugr_validator; then
    "hugr_validator not found in path"
    exit 1
fi

declare -a FAILED_TEST_NAMES
declare -a FAILED_TEST_MSGS
UNEXPECTED_PASSES=
NUM_FAILURES=0

for dir in test/compilation/output test/hugr/output; do
    for json in $(find $dir -maxdepth 1 -name "*.json"); do
        echo Validating "$json"
        RESULT=$(cat "$json" | hugr_validator 2>&1)
        if [ $? -ne 0 ]; then
            FAILED_TEST_NAMES[NUM_FAILURES]=$json
            FAILED_TEST_MSGS[NUM_FAILURES]=$RESULT
            NUM_FAILURES=$((NUM_FAILURES + 1))
        fi
    done

    for invalid_json in $(find test/compilation/output -maxdepth 1 -name "*.json.invalid"); do
        if (hugr_validator < $invalid_json 2>/dev/null > /dev/null); then
            UNEXPECTED_PASSES="$UNEXPECTED_PASSES $invalid_json"
        fi
    done
done

RED='\033[0;31m'
GREEN='\033[0;32m'
NO_COLOUR='\033[0m'

RESULT=0 # I.e., an "ok" exit value

if [ $NUM_FAILURES -gt 0 ]; then
    echo -e $RED
    for ix in $(seq 0 $((NUM_FAILURES - 1))); do
        echo Validation failed: "${FAILED_TEST_NAMES[$ix]}"
        echo "${FAILED_TEST_MSGS[$ix]}"
    done

    echo $NUM_FAILURES failures. $NO_COLOUR
    RESULT=1 # I.e. a "bad" exit value
else
    echo -e $GREEN All Hugrs validated $NO_COLOUR
fi

if [ "$UNEXPECTED_PASSES" != "" ]; then
    echo -e $RED "There were unexpected passes: $UNEXPECTED_PASSES" $NO_COLOUR
    RESULT=1
fi
exit $RESULT
