#!/bin/bash

allTests=`find SpiderMonkey/$1 -name "*.js" | \
          grep -vE "(shell\\.js)|(template\\.js)"`

failures=$((0))
numTests=$((0))
for testCase in $allTests
  do
    numTests=$((numTests+1))
    ./spidermonkey_test.sh $testCase || failures=$((failures+1))
  done


echo "$numTests test(s) tried. $failures test(s) failed."