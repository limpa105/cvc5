#!/bin/bash

TEST_DIR=$1
CVC5="build/bin/cvc5"
output_file=$2
sat_count=0
total=0


if [ ! -f "$output_file" ]; then
    # The file doesn't exist, so create it using touch
    touch "$output_file"
else
    > "$output_file"
fi

echo $1
echo $2 

# first check non nested directroies
for file in "$TEST_DIR"/*; do
    if [ -f "$file" ]; then
        ((total++))
        filename="exp/${file##*/}"
        echo -n "$file " >> "$output_file"
        if timeout 1200s $CVC5 --local-search-ext --produce-models --check-models   "$file" >  "$filename" 2>&1; then
            ((sat_count++))
            echo "Processed $file"
        else
            echo "timeout" >> "$output_file"
            echo "Time out $file"
        fi 
    fi
done 

for file in "$TEST_DIR"/*/*; do
    if [ -f "$file" ]; then
        ((total++))
        echo -n "$file " >> "$output_file"
        if timeout 1200s $CVC5 --local-search-ext --produce-models --check-models -v "$file" >>  "$output_file"; then
            ((sat_count++))
            echo "Processed $file"
        else
            echo "timeout" >> "$output_file"
            echo "Time out $file"
        fi 
    fi
done 

for file in "$TEST_DIR"/*/*/*; do
    if [ -f "$file" ]; then
        ((total++))
        echo -n "$file " >> "$output_file"
        if timeout 1200s $CVC5 --local-search-ext --produce-models --check-models -v "$file" >>  "$output_file"; then
            ((sat_count++))
            echo "Processed $file"
        else
            echo "timeout" >> "$output_file"
            echo "Time out $file"
        fi 
    fi
done 

for file in "$TEST_DIR"/*/*/*/*; do
    if [ -f "$file" ]; then
        ((total++))
        echo -n "$file " >> "$output_file"
        if timeout 1200s $CVC5 --local-search-ext --produce-models --check-models -v "$file" >>  "$output_file"; then
            ((sat_count++))
            echo "Processed $file"
        else
            echo "timeout" >> "$output_file"
            echo "Time out $file"
        fi 
    fi
done 



echo "$sat_count correct out of $total"
