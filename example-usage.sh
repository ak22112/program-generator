#!/usr/bin/env bash

# WARN: THIS SCRIPT IS NOT MEANT TO BE RUN

# This is an example of how you might use the program generator.
#
# The generator is deterministic, meaning that for any grammar and seed,
# it will return the same, single string every time it is run.
#
# To batch generate programs, a wrapper script is required to make repeated
# calls to the generator while providing different random seeds.
#
# At the time of writing, I am not familiar with Agda's IO module, so I don't
# know exactly how it handles getting user input. So this script is just to
# show how batch generation *could* work.

num_programs=$1

if ! [[ $num_programs =~ ^[0-9]+$ ]]; then
  echo "Usage: $0 <positive integer>"
  exit 1
fi

for ((i = 0; i < num_programs; i++)); do
  ./program-generator "$RANDOM"
done
