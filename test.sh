#! /bin/sh
RUST_BACKTRACE=1 cargo run -- --print-ast --print-mir \
  language/test/test.cf || \
  echo "failure to compile : " $? && exit
#cc test.o -o test || echo "failure to link" && exit
#rm test.o || echo "failure to remove" && exit
#echo
#echo === RUNNING ===
#echo
#./test
#echo "exit code: " $?
