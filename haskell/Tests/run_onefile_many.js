#!/bin/bash

if [ $# -ne 2 ]
then
  echo "Usage: `basename $0` testfile impllist"
  echo "Ex: `basename $0` lawl.js \"lambdajs\""
  exit 65
fi

for impl in $2 
do
  ./impl.$impl $1
done
