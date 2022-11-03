

filenamesIn = ["blog1/blog1", "blog2/blog2", "blog3/blog3", "blog4/blog4", "blog5/blog5", "blog6/blog6", "blog7/blog7", "blog8/blog8", "blog9/blog9", "blog10/blog10"]

for files in filenamesIn:
    filenameOut = files + "Out" + ".txt"
    file = open(files + ".txt", 'r')
    characters = []

    while True:
        read = file.read(1)
        characters.append(read + "\n")
        if not read:
            break

    file.close()

    print("Length of characters is " + str(len(characters)))
    
    with open(filenameOut, 'w') as fOut:
        for char in characters:
            fOut.write(char)
