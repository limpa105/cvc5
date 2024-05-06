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
        echo -n "NEW FILE" >> "$output_file"
        echo -n "$file " >> "$output_file"
	echo >> "$output_file"
	    $CVC5 --local-search-ext --produce-models --check-models --stats --tlimit=1200000  "$file" >> "$output_file" 2>&1
        echo "Processed $file"
    fi
done 

for file in "$TEST_DIR"/*/*; do
    if [ -f "$file" ]; then
        ((total++))
        echo -n "NEW FILE" >> "$output_file"
        echo -n "$file \n" >> "$output_file"
	echo >> "$output_file"
	    $CVC5 --local-search-ext --produce-models --check-models --stats --tlimit=1200000  "$file" >> "$output_file" 2>&1
        echo "Processed $file"
    fi
done 

for file in "$TEST_DIR"/*/*/*; do
    if [ -f "$file" ]; then
        ((total++))
        echo -n "NEW FILE" >> "$output_file"
        echo -n "$file \n" >> "$output_file"
	echo >> "$output_file"
	    $CVC5 --local-search-ext --produce-models --check-models --stats --tlimit=1200000  "$file" >> "$output_file" 2>&1
        echo "Processed $file"
    fi
done 


for file in "$TEST_DIR"/*/*/*/*; do
    if [ -f "$file" ]; then
        ((total++))
        echo -n "NEW FILE" >> "$output_file"
        echo -n "$file \n" >> "$output_file"
	echo >> "$output_file"
	    $CVC5 --local-search-ext --produce-models --check-models --stats --tlimit=1200000  "$file" >>  "$output_file" 2>&1
        echo "Processed $file"
    fi
done  

python3 analyze.py "$output_file"
