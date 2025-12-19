#!/bin/bash

runFile () {
  echo 'Execute files:' "$1"
  command="ghc $1 -o build/Main -odir build -hidir build"
  if ${command}
  echo ''
  then
    echo '======== run Main ========'
    ./build/Main
  else
    echo '======== FAILED BUILD ========'
  fi
}


mkdir -p build
if  [[ $1 = "--all" ]]; then
    echo "Option --all turned on"
    allFilesInSrc=$(find src -name '*.hs' | tr '\n' ' ')
    runFile "$allFilesInSrc"
else
    runFile "src/Main.hs src/Extra.hs"
fi
