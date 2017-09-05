#! /bin/sh
cargo run -- --print-ast language/scratch.cf || \
  echo "failure to compile : " $? && exit
