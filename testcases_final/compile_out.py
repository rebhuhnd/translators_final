## Run this script to generate output of cases.
## Note: this does not remove .out files that have been generated, they just overwrite the ones that exist.

import os
import subprocess
import time

for infile in os.listdir("./"):	
    if infile.endswith(".in"):
        parts = infile.split(".")
        outfile = parts[0]+".out"				
        os.system("python " + infile + " > " + outfile)