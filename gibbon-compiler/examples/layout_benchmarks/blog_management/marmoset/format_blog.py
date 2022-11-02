
filenameIn = "blog1.txt"
filenameOut = "blog1_gibbon.txt"

file = open(filenameIn, 'r')

characters = []

while True:

    read = file.read(1)
    characters.append(read + "\n")
    if not read:
        break

file.close()


with open(filenameOut, 'w') as fOut:
    for char in characters:
        fOut.write(char)
