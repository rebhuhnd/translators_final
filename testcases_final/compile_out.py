## Run this script to generate output of cases.

import os

for infile in os.listdir("./"):
	if infile.endswith(".in"):
		parts = infile.split(".")
		outfile = parts[0]+".out"
		print "Generating " + outfile + " from " + infile + "..."
		os.system("rm *.out")
		os.system("python "+infile+" > "+outfile)

