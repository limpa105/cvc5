import pandas as pd 
import sys 

def make_df(entries):
    data = {}
# Extract column names and values
    entries = [i for i in entries if "=" in i]
    for entry in entries:
        parts = entry.split("=")
        if len(parts) == 2:
            column = parts[0].strip()
            value = parts[1].strip()
            if column not in data:
                data[column] = []
            data[column].append(value)
    df = pd.DataFrame(data)
    return df 


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python script.py <filename>")
        sys.exit(1)
    filename = sys.argv[1]
    with open(filename, "r") as file:
    # Read entire file contents
        file_contents = file.read()
    file_contents = file_contents.split("NEW FILE")
    result = []
    for i in file_contents:
        result.append(i.split("\n"))
    df = pd.DataFrame()
    for i in result:
        df = pd.concat([df, make_df(i)],ignore_index=True, join='outer', sort=False)
    print(df.columns)
    if "CVC5::SolutionFoundByLS" not in df.columns:
        df["CVC5::SolutionFoundByLS"] = 0
    if "CVC5::SolutionFoundBySimplex" not in df.columns:
        df["CVC5::SolutionFoundBySimplex"] =0
    if "Simplex::RunTime" not in df.columns:
        df["Simplex::RunTime"] ='0'
    if "LS::RunTime" not in df.columns:
        df["LS::RunTime"] ='0'
    if "theory::arith::pivots" not in df.columns:
        df["theory::arith::pivots"] = 0
    df["CVC5::SolutionFoundByLS"] = df["CVC5::SolutionFoundByLS"].fillna('0').astype(int)
    df["CVC5::SolutionFoundBySimplex"] = df["CVC5::SolutionFoundBySimplex"].fillna('0').astype(int)
    df["theory::arith::pivots"] = df["theory::arith::pivots"].fillna('0').astype(int)
    df["LS::RunTime"] = df["LS::RunTime"].str.replace('ms', '').fillna('0').astype(int).sum()
    df["global::totalTime"] = df["global::totalTime"].str.replace('ms', '').fillna('0').astype(int).sum()
    df["Simplex::RunTime"] = df["Simplex::RunTime"].str.replace('ms', '').fillna('0').astype(int).sum()
    print("Total:", df.shape[0])
    print("Solved:", df["CVC5::SolutionFoundByLS"].sum() + df["CVC5::SolutionFoundBySimplex"].sum())
    print("Solutions Found By LS", df["CVC5::SolutionFoundByLS"].sum())
    print("Solutions Found By Simplex", df["CVC5::SolutionFoundBySimplex"].sum() )
    print("Avg LS running time", df["LS::RunTime"].sum()/df.shape[0])
    print("Avg Simplex running time", df["Simplex::RunTime"].sum()/df.shape[0])
    print("Avg RunTime Total", df["global::totalTime"].sum()/df.shape[0])
    print("LS to Simplex Time Ratio", (df["LS::RunTime"]/df["Simplex::RunTime"]).sum() * 0.001)  
    print("Avg number of pivots", (df["theory::arith::pivots"].sum()/df.shape[0]))     

    
