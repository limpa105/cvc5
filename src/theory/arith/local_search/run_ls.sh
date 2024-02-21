#!/bin/bash

TEST_DIR="../../../../test/regress/cli/regress0/idl/CAV_2009/"
CVC5="../../../../build/bin/cvc5"
output_file="picky_ls_cpp_results.txt"
sat_count=0
total=0

> "$output_file"

# first check non nested directroies
for file in "$TEST_DIR"/*/*/*; do
    if [ -f "$file" ]; then
        ((total++))
        if timeout 1200s "$CVC5" --local-search-ext --produce-models  "$file"; then
            ((sat_count++))
            echo "Processed $file"  >> "$output_file"
            echo "Processed $file"
        else
            echo "timeout for file $file" >> "$output_file"
            echo "Time out $file"
        fi 
    fi
done 
echo "$sat_count correct out of $total"

# Now check nested directories
for file in "$TEST_DIR"/*/*/*/*; do
    echo "$file"
    ((total++))
     if timeout 1200s "$CVC5" --local-search-ext --produce-models --check-models "$file"; then
          ((sat_count++))
          echo "Processed $file"  >> "$output_file"
          echo "Processed $file"
     else
         echo "timeout for file $file" >> "$output_file"
         echo "Time out $file"
     fi 
done 
echo "$sat_count correct out of $total"
