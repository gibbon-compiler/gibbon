import os 
import sys 
import argparse

num_call = 0

def writeCHeaders(code):

    code.append("#include <stdio.h>")
    code.append("#include <stdlib.h>")
    code.append("#include <time.h>")
    #code.append("#include \"globals.c\"")
    addNewLine(code)
    code.append("typedef char* CursorTy;")
    code.append("typedef int IntTy;")
    code.append("typedef char TagTy;")
    addNewLine(code)

def generate_k_field_list_dtype(numFields, code):

      
    # data List = Cons Int List | Nil
    # typedef struct {
    #    CursorTy dataConBuffer;
    #    CursorTy intBuffer;
    # } ConsIntList;
    
    # data List = Cons k1 k2 k3 ... List | Nil
    # typedef struct {
    #   CursorTy dataConBuffer; 
    #   CursorTy k1;
    #   CursorTy k2;
    #   CursorTy k3;
    #   .
    #   .
    #   .
    # } ConsKFieldList;


    code.append("typedef struct {")
    code.append("  CursorTy tagRegion;")

    for i in range(numFields):
        code.append("  CursorTy k" + str(i + 1) + ";")

    code.append("} Cons" + str(numFields) + "FieldList;")


def addNewLine(code):
    code.append("\n")

def writeCodeToFile(outFile, statement_list):
    with open(outFile, "w") as file:
        for statement in statement_list: 
            file.write(statement + "\n")


def generate_k_list_build_function(numFields, code):

    #generate the function header 
    addNewLine(code)
    listTypeName = "Cons" + str(numFields) + "FieldList"
    code.append(listTypeName + "* " + "mkList(" + listTypeName + " *inList, " + "IntTy listLength, " + listTypeName + " *startAddress" + "){")

    code.append("   if (listLength <= 0){")
    code.append("       *((TagTy*) inList->tagRegion) = '1';")
    code.append("       return startAddress;")
    code.append("   }")

    code.append("   else{")
    code.append("       *((TagTy*) inList->tagRegion) = '0';")
    code.append("       inList->tagRegion = inList->tagRegion + sizeof(TagTy);")

    for i in range(numFields):
        code.append("       *((IntTy*) inList->k" + str(i+1) + ") = listLength;")
        code.append("       inList->k" + str(i+1) + " = inList->k" + str(i+1) + " + sizeof(IntTy);")


    #generate recursive call 
    code.append("       " + listTypeName + " *returnedList = mkList(inList, listLength - 1, startAddress);")
    code.append("       return returnedList;")
    code.append("   }")

    code.append("}")
    addNewLine(code)


# def generate_k_list_build_function(numFields, code):

#     #generate the function header 
#     addNewLine(code)
#     listTypeName = "Cons" + str(numFields) + "FieldList"
#     code.append(listTypeName + "* " + "mkList(" + listTypeName + " *inList, " + "IntTy listLength, " + listTypeName + " *startAddress" + "){")

#     code.append("   if (listLength <= 0){")
#     code.append("       *((TagTy*) inList) = '1';")
#     code.append("       return startAddress;")
#     code.append("   }")

#     code.append("   else{")
#     code.append("       *((TagTy*) inList) = '0';")
#     code.append("       inList = inList + sizeof(TagTy);")

#     for i in range(numFields):
#         code.append("       *((IntTy*) inList) = listLength;")
#         code.append("       inList = inList + sizeof(IntTy);")


#     #generate recursive call 
#     code.append("       " + listTypeName + " *returnedList = mkList(inList, listLength - 1, startAddress);")
#     code.append("       return returnedList;")
#     code.append("   }")

#     code.append("}")
#     addNewLine(code)

def generate_copy_variable(numFields, copyFromVariable, code):

    addNewLine(code) 
    listTypeName = "Cons" + str(numFields) + "FieldList" 
    copyToVariable = copyFromVariable + "Copied"
    
    code.append("   " + listTypeName + " " + copyToVariable + ";")
    code.append("   " + copyToVariable + ".tagRegion" + " = " + copyFromVariable + "->tagRegion;" )

    for i in range(numFields):
        code.append("   " + copyToVariable + ".k" + str(i+1) + " = " + copyFromVariable + "->k" + str(i+1) + ";")
    
    addNewLine(code)
    return copyToVariable

def generate_list_print_function(numFields, code):
    
    addNewLine(code)
    listTypeName = "Cons" + str(numFields) + "FieldList"
    code.append("void printList(" + listTypeName + " *inList){")
    code.append("   TagTy tag = *((TagTy*) inList->tagRegion);")
    code.append("   inList->tagRegion = inList->tagRegion + 1;")
    code.append("   switch(tag){")
    code.append("       case '0': ")
    code.append("           printf(\"(Cons \");")
    
    for i in range(numFields):
            code.append("           IntTy val" + str(i+1) + " = *((IntTy*) inList->k" + str(i+1) +");")
            code.append("           printf(\"%d \", val" + str(i+1) + ");")
            code.append("           inList->k" + str(i+1) + " += sizeof(IntTy);")


    #generate the recursive call
    code.append("           printList(inList);")
    code.append("           break;")

    code.append("       case '1': ")
    code.append("           printf(\"(Nil))\\n\");")
    code.append("           break;")
    code.append("       default:")
    code.append("           break;")
    
    #end switch
    code.append("   }")

    code.append("}")  
    addNewLine(code)

def allocateList(allocatedListVar, numFields, listTypeName, code):
    
    addNewLine(code)
    code.append("   " + listTypeName + " *" + allocatedListVar + " = (" + listTypeName + "*" + ")" +  " malloc(sizeof(" + listTypeName + ")" + ");")

    code.append("   " + allocatedListVar + "->tagRegion = (CursorTy) malloc(sizeof(char) * (listSize + 1));")
    
    for i in range(numFields):
        code.append("   " + allocatedListVar + "->k" + str(i + 1) + " = " + "(CursorTy)" + " malloc(sizeof(IntTy) * listSize);")
    
    addNewLine(code)


def generate_call(indentation, callName, returnTy, args, code=None):
    
    global num_call

    #generate arguments 
    
    argsStr = ""
    for i in range(len(args)):
        argsStr += args[i] 
        if (i != len(args) - 1):
            argsStr += ", "
    
    call_code = []
    returnedVar = None
    if (returnTy == "void"):
        call_code.append(indentation + callName + "(" + argsStr + ");" )
    else:
        returnedVar = "call" + str(num_call)
        num_call = num_call + 1
        call_code.append(indentation + returnTy + " " + returnedVar + " = " + callName + "(" + argsStr + ");" )
    
    if code == None: 
        return (returnedVar, call_code)
    else:
        code.append(call_code[0])
        return returnedVar
    
def time_call(indentation, callCode, code):

    code.append(indentation + "clock_t start, end;")
    code.append(indentation + "double cpu_time_used;")

    code.append(indentation + "start = clock();")
    code.extend(callCode)
    code.append(indentation + "end = clock();")

    cpu_time_used_var = "cpu_time_used"

    code.append(indentation + "cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;")

    return cpu_time_used_var

def generate_add1_recursive(numFields, code, useKFields):

    addNewLine(code)
    listTypeName = "Cons" + str(numFields) + "FieldList"
    code.append(listTypeName + " *" + "add1Recursive(" + listTypeName + " *inRegion, " + listTypeName + " *newRegion, " + listTypeName + " *startAddress" + "){")
    
    #write function body of add1 

    code.append("   " + "TagTy tag = *((TagTy*) inRegion->tagRegion);")
    code.append("   " + "inRegion->tagRegion += 1;")
    code.append("   " + "*((TagTy*) newRegion->tagRegion) = tag;")
    code.append("   " + "newRegion->tagRegion += 1;")
    code.append("   " + "switch(tag){")
    code.append("           " + "case '0':")
    code.append("                   " + ";")

    for i in range(useKFields):
        code.append("                   " + "IntTy val" + str(i+1) + " = " + "*((IntTy*) inRegion->k" + str(i+1) + ");")
        code.append("                   " + "inRegion->k" + str(i+1)  + " += " + "sizeof(IntTy);")
        code.append("                   " + "*((IntTy*) newRegion->k" + str(i+1) + ")" + " = " + "val" + str(i+1) + " + 1;")
        code.append("                   " + "newRegion->k" + str(i+1) + " += " + "sizeof(IntTy);")


    #still need to copy unused fields. 
    for i in range(useKFields, numFields):
        code.append("                   " + "IntTy val" + str(i+1) + " = " + "*((IntTy*) inRegion->k" + str(i+1) + ");")
        code.append("                   " + "inRegion->k" + str(i+1)  + " += " + "sizeof(IntTy);")
        code.append("                   " + "*((IntTy*) newRegion->k" + str(i+1) + ")" + " = " + "val" + str(i+1) + ";")
        code.append("                   " + "newRegion->k" + str(i+1) + " += " + "sizeof(IntTy);")
    
    #generate recursive call to add 1
    code.append("                   " + "return add1Recursive(inRegion, newRegion, startAddress);")
    code.append("                   " + "break;")

    #generate case Nil 
    code.append("           " + "case '1':")
    code.append("                   " + ";")
    code.append("                   " + "return startAddress;")
    code.append("                   " + "break;")

    #generate default case 
    code.append("           " + "default:")
    code.append("                  " + ";")
    code.append("                  " + "break;")
    code.append("   " + "}")

    code.append("}")
    addNewLine(code) 
    return

def generate_add1_iterative(numFields, code, useKFields):

    addNewLine(code)
    listTypeName = "Cons" + str(numFields) + "FieldList"
    code.append("void" + " add1Iterative(" + listTypeName + " *inRegion" + ")" + "{")
    code.append("   " + "TagTy tag = *((TagTy*) inRegion->tagRegion);")
    code.append("   " + "CursorTy tagCursor = inRegion->tagRegion;")

    for i in range(useKFields):
        code.append("   " + "CursorTy k" + str(i+1) + " = " + "inRegion->k" + str(i+1) + ";")

    code.append("   " + "while(tag != '1'){")
    
    for i in range(useKFields):
        code.append("       " + "*((IntTy*) k" + str(i+1) + ") += 1;")
        code.append("       " + "k" + str(i+1) + " += sizeof(IntTy);")

    code.append("       " + "tagCursor += 1;")
    code.append("       " + "tag = *((TagTy*) tagCursor);") 
    code.append("   " + "}")
    code.append("}")
    addNewLine(code)
    return

def generate_add1_iterative_opt(numFields, code, useKFields):
    
    addNewLine(code)
    listTypeName = "Cons" + str(numFields) + "FieldList"
    code.append("void" + " add1IterativeOpt(" + listTypeName + " *inRegion, " +  "IntTy listSize" + ")" + "{")

    for i in range(useKFields):
        code.append("   " + "CursorTy k" + str(i+1) + " = " + "inRegion->k" + str(i+1) + ";")

    code.append("   " + "for (int i = 0; i < listSize; i++){")
    for i in range(useKFields):
        code.append("           " + "*((IntTy*) k" + str(i+1) + ")" + " = " + "*((IntTy*) k" + str(i+1) +")" + " + 1;")
        code.append("           " + "k" + str(i+1) + " += " + "sizeof(IntTy);")

    code.append("   }")

    code.append("}")  
    addNewLine(code)

    return

def generate_main(numFields, gen_function, listSize, printList, code):
    
    listTypeName = "Cons" + str(numFields) + "FieldList"
    listTypeNameTy = listTypeName + "*"
    listInitializeVar = "initList"
    code.append("int main(){")
    
    #write all function definitions
    addNewLine(code)
    code.append("   " + "IntTy listSize = " + str(listSize) + ";")
    allocateList(listInitializeVar, numFields, listTypeName, code)

    #make a copy for the list initialize variable 
    copiedInitList = generate_copy_variable(numFields, listInitializeVar, code)

    #call mkList function 
    #variableMkListOut = "mkListOut"
    #code.append("   " + listTypeName + " *mkListOut " + "=" + " mkList(" + listInitializeVar + ", listSize, " + "&" + copiedInitList + ");")
    variableMkListOut = generate_call("   ", "mkList", listTypeNameTy, [listInitializeVar, "listSize", "&" + copiedInitList], code)

    newMemForAdd1 = "add1NewMem"
    allocateList(newMemForAdd1, numFields, listTypeName, code)

    #generate copy for add1NewMem
    newMemForAdd1Copy = generate_copy_variable(numFields, newMemForAdd1, code)

    #call add1Recursive
    callCode = []
    variableAdd1ListOut = "" 
    if gen_function == "add1Recursive":
        (variableAdd1ListOut, callCode) = generate_call("   ", "add1Recursive", listTypeNameTy, [variableMkListOut, newMemForAdd1, "&" + newMemForAdd1Copy])
        time_used_var = time_call("   ", callCode, code)
        code.append("   " + "printf(\"The time taken by add1 was %f seconds.\\n\", " + time_used_var + ");")
        if printList:
            code.append("   " + "printList(" + variableAdd1ListOut + ");")
    elif gen_function == "add1Iterative":
        (variableAdd1ListOut, callCode) = generate_call("   ", "add1Iterative", "void", [variableMkListOut])
        time_used_var = time_call("   ", callCode, code)
        if printList:
            code.append("   " + "printList(" + variableMkListOut + ");")
        code.append("   " + "printf(\"The time taken by add1 was %f seconds.\\n\", " + time_used_var + ");")
    elif gen_function == "add1IterativeOpt":
        (variableAdd1ListOut, callCode) = generate_call("   ", "add1IterativeOpt", "void", [variableMkListOut, "listSize"])
        time_used_var = time_call("   ", callCode, code)
        if printList:
            code.append("   " + "printList(" + variableMkListOut + ");")
        code.append("   " + "printf(\"The time taken by add1 was %f seconds.\\n\", " + time_used_var + ");")


    code.append("}")



if __name__ == "__main__":

    parser = argparse.ArgumentParser(description="This program generates a list with k field and autogenerates and times associated functions.\n")
    
    # Add arguments
    parser.add_argument('--k', type=int, help='The number of fields to generate in a Cons list.', required=True)
    parser.add_argument('--l', type=int, help='The number of fields to traverse.', required=True)
    parser.add_argument('--outFile', type=str, help='The name of the file to store the output to.', required=True)
    parser.add_argument('--function', type=str, choices=['add1Recursive', 'add1Iterative', 'add1IterativeOpt'], help='The name of the function to generate code for.', required=True)
    parser.add_argument('--list_size', type=int, help='The size of the cons list.', required=True)
    parser.add_argument('--print_list', type=bool, default=False, help='Print the final cons list.')

    args = parser.parse_args()
    numFields  = args.k
    numUsedFields = args.l
    outputFile = args.outFile
    gen_function = args.function
    listSize = args.list_size 
    printList = args.print_list
    
    code = []
    writeCHeaders(code)
    generate_k_field_list_dtype(numFields, code)
    generate_k_list_build_function(numFields, code)
    generate_list_print_function(numFields, code)
    generate_add1_recursive(numFields, code, numUsedFields)
    generate_add1_iterative(numFields, code, numUsedFields)
    generate_add1_iterative_opt(numFields, code, numUsedFields)
    generate_main(numFields, gen_function, listSize, printList, code)
    writeCodeToFile(outputFile, code) 


