import random

filenamesIn = [ 
"blog1/blog1", 
"blog2/blog2", 
"blog3/blog3", 
"blog4/blog4", 
"blog5/blog5", 
"blog6/blog6", 
"blog7/blog7", 
"blog8/blog8", 
"blog9/blog9", 
"blog10/blog10"]

'''for files in filenamesIn:
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

    random_keyowrds = random.choices(words, k=500)
    
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
            fOut.write(char)'''

def is_prime(n):
    
    if (n == 0):
        return False 
    
    if (n == 1):
        return True

    for i in range(2, n):
        if (n%i == 0):
            return False

    return True

for files in filenamesIn:
    randomlist = random.sample(range(0, 100000), 1000)
    
    primes = [] 
    for i in randomlist:
        if (is_prime(i)):
            primes.append(i)   

    filenameIn  = files + ".txt"
    filenameOut = files + "Out" + ".txt"
    tagfile = files + "Tag.txt"

    num_string = " ".join(map(str,randomlist)) 
    num_primes = " ".join(map(str,primes)) 

    num_string = str(num_string)
    num_primes = str(num_primes)

    #for char in num_string: 
    #    print(char)

    #print(num_string)
    #print(num_primes)

    with open(filenameIn, 'w') as fIn:
        for num in randomlist:
            fIn.write(str(num) + " ")
    
    out_char = 0
    with open(filenameOut, 'w') as fOut:
        for char in num_string:
            fOut.write(char + "\n")
            out_char += 1 

    print("Character count for " + str(filenameOut) + " is " + str(out_char) )
    
    out_tag = 0
    with open(tagfile, 'w') as fTag:
        for char in num_primes:
            fTag.write(char + "\n")
            out_tag += 1
    
    print("Character count for " + str(tagfile) + " is " + str(out_tag) ) 
