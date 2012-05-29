#!/bin/bash

if [ $# -ne 1 ]
then
  echo "Usage: `basename $0` testname.js"
  exit 65
fi

./dist/build/lambdaJS/lambdaJS --test-cases < $1 | ../Redex/test-shell.ss
