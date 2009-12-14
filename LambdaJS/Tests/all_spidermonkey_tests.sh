#!/bin/bash

if [ $# -ne 1 ]
then
  echo "Usage: `basename $0` thirdpartyimpl"
  echo "Ex: `basename $0` v8"
  exit 65
fi

allTests=`find SpiderMonkey -name "*.js" | \
          grep -vE "(shell\\.js)|(template\\.js)"`

failures=$((0))
thirdpartyfailures=$((0))
numTests=$((0))

function proc_failure {
  retcode=$?
  if [[ $retcode == 1 ]]; then
    echo "FAILED on $src"
    failures=$((failures+1))
  fi
  if [[ $retcode == 2 ]]; then
    echo "THIRD PARTY FAILED on $src"
    thirdpartyfailures=$((thirdpartyfailures+1))
  fi
}


gold=$1
for testCase in $allTests
do
  numTests=$((numTests+1))
  ./spidermonkey_test.sh $testCase $gold || proc_failure
done

echo "$numTests test(s) tried. $failures test(s) failed. $thirdpartyfailures third party test(s) failed."