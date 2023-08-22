import os 
import subprocess
import re
import statistics as stat

iterations = 9

rootdir = "/home/shay/a/singhav/gibbon/microbench/tail_recursion"


FILES = ["add1List.autoropes", "add1List.tailrec"]

Timings = {}

#Compilation phase
for file in FILES:
        
        gibbon_file_name = file

        gibbon_cmd = "gcc -O3 " + file + ".c" + " -o " + gibbon_file_name
        
        print("The gcc command was: ")
        print()
        print(gibbon_cmd)
        print()

        gibbon_cmd_c = subprocess.run(["gcc", "-O3" , file + ".c",  "-o", gibbon_file_name])
        print()

        print("The exit code for the gcc compilation was %d" % gibbon_cmd_c.returncode)



#run the files and get the timings
iterations = 15

for size in range(1000000, 11000000, 1000000):
    for files in FILES:

            times = [] 
            gibbon_binary = files
            
            print()
            print("Running the binary " + str(gibbon_binary))
            print()

            for i in range(iterations): 

                file_stats = gibbon_binary + ".txt"
            
                cmd =  "(" + "cd " + rootdir + " && " + "(" + "./" + gibbon_binary + " " + str(size) + " > " + file_stats + ")" + ")"

                print(cmd)

                gibbon_binary_cmd = subprocess.call(cmd, shell=True)

                data = open(file_stats, 'r').read()  

                exec_time = re.findall("Execution time: (.*)", data)
                times.append(float(exec_time[0])) 
            
            print()
            print(times)

            averageTimes = float (sum(times) / iterations)
            medianTimes  = stat.median(times)

            tupleTimes = (averageTimes, medianTimes)

            Timings[(gibbon_binary, size)] = tupleTimes

            print()

print(Timings)

f = open("experiment_timings_add2.txt", "w")

for key, value in Timings.items():
    f.write('%s:(average:%s, median:%s)\n' % (key, value[0], value[1]))

f.close()