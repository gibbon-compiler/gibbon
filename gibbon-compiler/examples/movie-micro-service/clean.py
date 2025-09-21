# modified based on clean.py from blog management
import os 
import subprocess

gibbon_file_names = ["test","testInsertmovie", "testSearchMovie", "testDeleteMovie"]

# layouts = ["layout1", "layout2", "layout3", "layout4", "layout5", "layout6", "layout7", "layout8"]

print("Cleaning out the c files and binaries")

#Compilation phase
for file_name in gibbon_file_names:

    filename_c = file_name + ".c"
    filename_exe = file_name + ".exe"
    gibbon_cmd_c = subprocess.run(["rm",  filename_c])
    gibbon_cmd_bin = subprocess.run(["rm",  filename_exe])
    gibbon_cmd_bin = subprocess.run(["rm",  file_name])


