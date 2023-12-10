import os 
import subprocess
import re

iterations = 9

rootdir = "/local/scratch/a/singhav/Applications/src/gibbon/gibbon-compiler/examples/layout_benchmarks/blog_management/marmoset/"

ut_hash_include = "/local/scratch/a/singhav/Applications/src/uthash-2.3.0/include"

Passes = ["ContentSearch", "DeleteTag", "InsertTag", "TagSearch"]

layouts = ["layout1", "layout2", "layout3", "layout4", "layout5", "layout6", "layout7", "layout8"]

#Compilation phase
for myPass in Passes:
    for layout in layouts: 
        
        gibbon_file_name = layout + myPass

        print()
        print("Trying compilation for file " + gibbon_file_name + ".hs")
        print()

        filename_haskell = gibbon_file_name + ".hs" 

        haskell_cmd = "gibbon --packed --no-gc --toC " + filename_haskell

        print("The haskell command was: ")
        print()
        print(haskell_cmd)
        print()

        gibbon_cmd_haskell = subprocess.run(["gibbon", "--packed", "--no-gc", "--toC", filename_haskell]) 

        print("The exit code for the haskell command was %d" % gibbon_cmd_haskell.returncode)
        print() 

        filename_c = gibbon_file_name + ".c"

        gibbon_cmd = "gcc" + " -O3 " + "-I" + ut_hash_include + " " + filename_c + " -o " + gibbon_file_name
        
        print("The gcc command was: ")
        print()
        print(gibbon_cmd)
        print()

        gibbon_cmd_c = subprocess.run(["gcc", "-O3", "-I" + ut_hash_include , filename_c,  "-o", gibbon_file_name])
        print()

        print("The exit code for the gcc compilation was %d" % gibbon_cmd_c.returncode)



Timings = {}

#run the files and get the timings

for myPass in Passes:
    for layout in layouts: 

        gibbon_binary = layout + myPass
        
        print()
        print("Running the binary " + str(gibbon_binary))
        print()

        file_stats = gibbon_binary + ".txt"
        
        cmd =  "(" + "cd " + rootdir + " && " + "(" + "./" + gibbon_binary + " --RUN " + str(iterations) + " > " + file_stats + ")" + ")"

        print(cmd)

        gibbon_binary_cmd = subprocess.call(cmd, shell=True)

        data = open(file_stats, 'r').read()  

        batch_time  = re.findall("BATCHTIME: (.*)", data) 
        median_time = re.findall("SELFTIMED: (.*)", data)
        
        print()
        print(batch_time)
        print(median_time)
       
        print(float(batch_time[0]))
        print(float(median_time[0]))
        
        batchTimes = float(batch_time[0])
        medianTimes = float(median_time[0])

        averageTimes = float (batchTimes / iterations)
        
        tupleTimes = (averageTimes, medianTimes)

        print(tupleTimes)

        Timings[gibbon_binary] = tupleTimes

        print()

print(Timings)

f = open("experiment_timings_marmoset.txt", "w")

for key, value in Timings.items():
    f.write('%s:(average:%s, median:%s)\n' % (key, value[0], value[1]))

f.close()
