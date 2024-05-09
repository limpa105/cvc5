import pandas as pd 
import sys 



if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python script.py <filename>")
        sys.exit(1)
    filename = sys.argv[1]
    with open(filename, "r") as file:
    # Read entire file contents
        file_contents = file.read()
    file_contents = file_contents.split("\n")[:-1]
    print(file_contents)
    unsat = 0
    for i in file_contents:
        if "unsat" in i:
            unsat +=1
    print("Unsat ", unsat, "out of ", len(file_contents))

