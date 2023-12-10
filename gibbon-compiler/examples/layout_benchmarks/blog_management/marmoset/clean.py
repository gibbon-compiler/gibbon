import os 
import subprocess

Passes = ["ContentSearch", "DeleteTag", "InsertTag", "TagSearch"]

layouts = ["layout1", "layout2", "layout3", "layout4", "layout5", "layout6", "layout7", "layout8"]

print("Cleaning out the c files and binaries")

#Compilation phase
for myPass in Passes:
    for layout in layouts: 

        gibbon_file_name = layout + myPass
        filename_c = gibbon_file_name + ".c"
        gibbon_cmd_c = subprocess.run(["rm",  filename_c])
        gibbon_cmd_bin = subprocess.run(["rm",  gibbon_file_name])



