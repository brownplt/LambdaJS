#!/bin/bash
if [ $# -ne 1 ]
then
  echo "Usage: `basename $0` infile.js"
  exit 65
fi

./dist/build/lambdaJS/lambdaJS +RTS -K100m -RTS --desugar < $1
