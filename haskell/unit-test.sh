#!/bin/bash

for file in `find Tests/UnitTests -name "*.tst"`
  do 
    echo "Running test suite $file..."
    ./dist/build/lambdaJS/lambdaJS --test-cases < $file | ../Redex/test-shell.ss
  done
