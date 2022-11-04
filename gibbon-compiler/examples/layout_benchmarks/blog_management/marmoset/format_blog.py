import random

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
    
    words = []
    with open(files + ".txt" ,'r') as file:
        for line in file:        
            for word in line.split():  
                words.append(word)

    random_keyowrds = random.choices(words, k=10)
    
    tagfile = files + "Tag.txt"
   
    tag_char_counter = 0

    with open(tagfile, 'w') as fTag:
        for word in random_keyowrds:
            for char in word:
                fTag.write(char + "\n")
                tag_char_counter = tag_char_counter + 1
            fTag.write(" \n")
            tag_char_counter = tag_char_counter + 1

    print("Length of the character in thr taglist is " + str(tag_char_counter))

    print("Length of characters is " + str(len(characters)))
    
    with open(filenameOut, 'w') as fOut:
        for char in characters:
            fOut.write(char)
