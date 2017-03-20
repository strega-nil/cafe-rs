#! /bin/sh
cargo run -- --print-mir --print-llir -o test.o src/test/test.pnk || \
  echo "failure to compile : " $? && exit
cc test.o -o test || echo "failure to link" && exit
rm test.o || echo "failure to remove" && exit
echo
echo === RUNNING ===
echo
./test
echo "exit code: " $?
