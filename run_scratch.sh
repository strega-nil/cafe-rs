#! /bin/sh
cargo run -- --print-ast --print-mir language/scratch.cf || \
  echo "failure to compile : " $? && exit
