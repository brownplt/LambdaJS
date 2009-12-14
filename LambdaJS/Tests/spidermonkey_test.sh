#!/bin/bash

if [ $# -ne 2 ]
then
  echo "Usage: `basename $0` fulltestpath thirdpartyimpl"
  echo "Ex: `basename $0` SpiderMonkey/Object/class-001 v8"
  exit 65
fi

src=$1

echo "Running on $1 ..."
goldImpl=$2
testPath=`mktemp -t lambdaJS1`
goldOutput=`mktemp -t lambdaJS2`
newOutput=`mktemp -t lambdaJS3`

trap "rm -f $testPath $goldOutput $newOutput" EXIT

function failure3rd {
  echo "THIRD PARTY FAILED on $src"
  exit 2
}

function failure {
  echo "FAILED on $src"
  exit 1
}

./assemble_spidermonkey_test.py $1 > $testPath || failure
./impl.$goldImpl $testPath > $goldOutput || failure3rd
#third party must have PASSED every test
didfail=`grep FAILED $goldOutput`
if [[ $didfail != "" ]];
then
  failure3rd
fi

newImpl=lambdajs
./impl.$newImpl $testPath > $newOutput || failure
diff=`diff $goldOutput $newOutput`
expected=`echo -e "\n"`
if [[ $diff == $expected ]]; then
  #do nothing
  z=0
else
  echo $diff
  failure
fi

echo "Success on $1"
