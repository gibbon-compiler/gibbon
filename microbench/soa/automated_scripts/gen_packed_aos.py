import os 
import sys 
import argparse

num_call = 0

def writeCHeaders(code):

    code.append("#include <stdio.h>")
    code.append("#include <stdlib.h>")
    code.append("#include <time.h>")
    code.append("#include <papi.h>")
    #code.append("#include \"globals.c\"")
    addNewLine(code)
    code.append("typedef char* CursorTy;")
    code.append("typedef int IntTy;")
    code.append("typedef char TagTy;")
    addNewLine(code)


def addNewLine(code):
    code.append("\n")

def writeCodeToFile(outFile, statement_list):
    with open(outFile, "w") as file:
        for statement in statement_list: 
            file.write(statement + "\n")


def generate_k_list_build_function(numFields, code):

    #generate the function header 
    addNewLine(code)
    listTypeName = "CursorTy"
    code.append(listTypeName + " " + "mkList(" + listTypeName + " inCursor, " + "IntTy listLength, " + listTypeName + " startAddress" + "){")

    code.append("   if (listLength <= 0){")
    code.append("       *((TagTy*) inCursor) = '1';")
    code.append("       return startAddress;")
    code.append("   }")

    code.append("   else{")
    code.append("       *((TagTy*) inCursor) = '0';")
    code.append("       inCursor = inCursor + sizeof(TagTy);")

    for i in range(numFields):
        code.append("       *((IntTy*) inCursor" + ") = listLength;")
        code.append("       inCursor += sizeof(IntTy);")


    #generate recursive call 
    code.append("       " + listTypeName + " returnedList = mkList(inCursor, listLength - 1, startAddress);")
    code.append("       return returnedList;")
    code.append("   }")

    code.append("}")
    addNewLine(code)

def generate_copy_variable(copyFromVariable, code):

    addNewLine(code) 
    listTypeName = "CursorTy" 
    copyToVariable = copyFromVariable + "Copied"
    
    code.append("   " + listTypeName + " " + copyToVariable + ";")
    code.append("   " + copyToVariable + " = " + copyFromVariable + ";")

    addNewLine(code)
    return copyToVariable

def generate_list_print_function(numFields, code):
    
    addNewLine(code)
    listTypeName = "CursorTy"
    code.append("void printList(" + listTypeName + " inList, " + "FILE *file" + "){")
    code.append("   TagTy tag = *((TagTy*) inList);")
    code.append("   inList = inList + 1;")
    code.append("   switch(tag){")
    code.append("       case '0': ")
    code.append("           fprintf(file, \"(Cons \");")
    
    for i in range(numFields):
            code.append("           IntTy val" + str(i+1) + " = *((IntTy*) inList" + ");")
            code.append("           fprintf(file, \"%d \", val" + str(i+1) + ");")
            code.append("           inList += sizeof(IntTy);")


    #generate the recursive call
    code.append("           printList(inList, file);")
    code.append("           break;")

    code.append("       case '1': ")
    code.append("           fprintf(file, \"(Nil))\\n\");")
    code.append("           break;")
    code.append("       default:")
    code.append("           break;")
    
    #end switch
    code.append("   }")

    code.append("}")  
    addNewLine(code)

def allocateList(allocatedListVar, numFields, listTypeName, code):

    num_bytes_per_cons_cell = "(" + "(" + "(1 + " + "(" + str(numFields) + " " + "* sizeof(IntTy)" + ")" + ") * listSize)" + " + 1)"

    addNewLine(code)
    code.append("   " + listTypeName + " " + allocatedListVar + " = (" + listTypeName + ")" +  " malloc(sizeof(" + "char" + ") * " + num_bytes_per_cons_cell + ");")
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

    #if (PAPI_start(EventSet) != PAPI_OK) {
    #fprintf(stderr, "PAPI start error!\n");
    #exit(1);
    #}

    code.append(indentation + "if (PAPI_start(EventSet) != PAPI_OK) {")
    code.append(indentation + "     " + "fprintf(stderr, \"PAPI start error!\\n\");")
    code.append(indentation + "     " + "exit(1);")
    code.append(indentation + "}")

    code.append(indentation + "clock_t start, end;")
    code.append(indentation + "double cpu_time_used;")

    code.append(indentation + "start = clock();")
    code.extend(callCode)
    code.append(indentation + "end = clock();")

    code.append(indentation + "if (PAPI_stop(EventSet, values) != PAPI_OK) {")
    code.append(indentation + "     " + "fprintf(stderr, \"PAPI stop error!\\n\");")
    code.append(indentation + "     " + "exit(1);")
    code.append(indentation + "}")

    #if (PAPI_stop(EventSet, values) != PAPI_OK) {
    #fprintf(stderr, "PAPI stop error!\n");
    #exit(1);
    #}

    cpu_time_used_var = "cpu_time_used"

    code.append(indentation + "cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;")

    return cpu_time_used_var

def generate_add1_recursive_out_of_place(numFields, code, useKFields):

    addNewLine(code)
    listTypeName = "CursorTy"
    code.append(listTypeName + " add1RecursiveOutOfPlace(" + listTypeName + " inRegion, " + listTypeName + " newRegion, " + listTypeName + " startAddress" + "){")
    
    #write function body of add1 

    code.append("   " + "TagTy tag = *((TagTy*) inRegion);")
    code.append("   " + "inRegion += 1;")
    code.append("   " + "*((TagTy*) newRegion) = tag;")
    code.append("   " + "newRegion += 1;")
    code.append("   " + "switch(tag){")
    code.append("           " + "case '0':")
    code.append("                   " + ";")

    for i in range(useKFields):
        code.append("                   " + "IntTy val" + str(i+1) + " = " + "*((IntTy*) inRegion" + ");")
        code.append("                   " + "inRegion" + " += " + "sizeof(IntTy);")
        code.append("                   " + "*((IntTy*) newRegion" + ")" + " = " + "val" + str(i+1) + " + 1;")
        code.append("                   " + "newRegion" + " += " + "sizeof(IntTy);")


    #still need to copy unused fields. 
    for i in range(useKFields, numFields):
        code.append("                   " + "IntTy val" + str(i+1) + " = " + "*((IntTy*) inRegion" + ");")
        code.append("                   " + "inRegion" + " += " + "sizeof(IntTy);")
        code.append("                   " + "*((IntTy*) newRegion" + ")" + " = " + "val" + str(i+1) + ";")
        code.append("                   " + "newRegion" + " += " + "sizeof(IntTy);")
    
    #generate recursive call to add 1
    code.append("                   " + "return add1RecursiveOutOfPlace(inRegion, newRegion, startAddress);")
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


def generate_add1_recursive_in_place(numFields, code, useKFields):

    addNewLine(code)
    listTypeName = "CursorTy"
    code.append(listTypeName + " add1RecursiveInPlace(" + listTypeName + " inRegion, " + listTypeName + " startAddress" + "){")
    
    #write function body of add1 

    code.append("   " + "TagTy tag = *((TagTy*) inRegion);")
    code.append("   " + "inRegion += 1;")

    code.append("   " + "switch(tag){")
    code.append("           " + "case '0':")
    code.append("                   " + ";")

    for i in range(useKFields):
        code.append("                   " + "*((IntTy*) inRegion) = " + "*((IntTy*) inRegion" + ") + 1;")
        code.append("                   " + "inRegion" + " += " + "sizeof(IntTy);")

     
    #skip unused fields 
    numFieldsLeft = numFields - useKFields;
    code.append("       " + "inRegion += " + str(numFieldsLeft) + " * " + "sizeof(IntTy);")
    
    #generate recursive call to add 1
    code.append("                   " + "return add1RecursiveInPlace(inRegion, startAddress);")
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

def generate_add1_iterative_in_place(numFields, code, useKFields):

    addNewLine(code)
    listTypeName = "CursorTy"
    code.append("void" + " add1IterativeInPlace(" + listTypeName + " inRegion" + ")" + "{")
    code.append("   " + "TagTy tag = *((TagTy*) inRegion);")
    code.append("   " + "CursorTy cursor = inRegion;")
    code.append("   " + "cursor += 1;")

    code.append("   " + "while(tag != '1'){")
    
    for i in range(useKFields):
        code.append("       " + "*((IntTy*) cursor" + ") += 1;")
        code.append("       " + "cursor" + " += sizeof(IntTy);")

    
    numFieldsLeft = numFields - useKFields

    code.append("       " + "cursor += " + str(numFieldsLeft) + " * " + "sizeof(IntTy);")
   
    code.append("       " + "tag = *((TagTy*) cursor);") 
    code.append("       " + "cursor += 1;")
    code.append("   " + "}")
    code.append("}")
    addNewLine(code)
    return


def generate_add1_iterative_out_of_place(numFields, code, useKFields):

    addNewLine(code)
    listTypeName = "CursorTy"
    code.append("void" + " add1IterativeOutOfPlace(" + listTypeName + " inRegion" + ", " + listTypeName + " outRegion" + ")" + "{")
    addNewLine(code)
    code.append("   " + "TagTy tag = *((TagTy*) inRegion);")
    code.append("   " + "CursorTy cursor = inRegion;")
    code.append("   " + "CursorTy outCursor = outRegion;")
    code.append("   " + "cursor += 1;")
    code.append("   " + "*((TagTy*) outCursor) = tag;")
    code.append("   " + "outCursor += 1;")

    addNewLine(code)

    code.append("   " + "while(tag != '1'){")
    
    for i in range(useKFields):
        code.append("       " + "*((IntTy*) outCursor" + ") = *((IntTy*) cursor) + 1;")
        code.append("       " + "cursor" + " += sizeof(IntTy);")
        code.append("       " + "outCursor" + " += sizeof(IntTy);")

    
    #numFieldsLeft = numFields - useKFields

    #code.append("       " + "cursor += " + str(numFieldsLeft) + " * " + "sizeof(IntTy);")
    #code.append("       " + "outCursor += " + str(numFieldsLeft) + " * " + "sizeof(IntTy);")

    for i in range(useKFields, numFields):
        code.append("                   " + "IntTy val" + str(i+1) + " = " + "*((IntTy*) cursor" + ");")
        code.append("                   " + "cursor" + " += " + "sizeof(IntTy);")
        code.append("                   " + "*((IntTy*) outCursor" + ")" + " = " + "val" + str(i+1) + ";")
        code.append("                   " + "outCursor" + " += " + "sizeof(IntTy);")

   
    code.append("       " + "tag = *((TagTy*) cursor);") 
    code.append("       " + "*((TagTy*) outCursor) = tag;")
    code.append("       " + "cursor += 1;")
    code.append("       " + "outCursor += 1;")
    code.append("   " + "}")
    code.append("}")
    addNewLine(code)
    return

def generate_papi_init_code(indentation, code):

    addNewLine(code)

    #int retval, EventSet = PAPI_NULL;
    #long long values[2];

    #retval = PAPI_library_init(PAPI_VER_CURRENT);
    #if (retval != PAPI_VER_CURRENT) {
    #    fprintf(stderr, "PAPI library init error!\n");
    #    exit(1);
    #}
    #
    #if (PAPI_create_eventset(&EventSet) != PAPI_OK)
    #    fprintf(stderr, "Error creating event set\n");
    #
    #if (PAPI_add_event(EventSet, PAPI_TOT_INS) != PAPI_OK)
    #    fprintf(stderr, "Error adding total instructions event\n");
    #
    #if (PAPI_add_event(EventSet, PAPI_L2_DCM) != PAPI_OK)
    #    fprintf(stderr, "Error adding load instructions event\n");

    code.append(indentation + "int retval, EventSet = PAPI_NULL;")
    code.append(indentation + "long long values[3];")

    code.append(indentation + "retval = PAPI_library_init(PAPI_VER_CURRENT);")
    code.append(indentation + "if (retval != PAPI_VER_CURRENT) {")
    code.append(indentation + "     " + "fprintf(stderr, \"PAPI library init error!\\n\");" )
    code.append(indentation + "     " + "exit(1);")
    code.append(indentation + "}")

    code.append(indentation + "if (PAPI_create_eventset(&EventSet) != PAPI_OK)")
    code.append(indentation + "     " + "fprintf(stderr, \"Error creating event set\\n\");")

    code.append(indentation + "if (PAPI_add_event(EventSet, PAPI_TOT_INS) != PAPI_OK)")
    code.append(indentation + "     " + "fprintf(stderr, \"Error adding total instructions event\\n\");")

    code.append(indentation + "if (PAPI_add_event(EventSet, PAPI_L2_TCM) != PAPI_OK)")
    code.append(indentation + "     " + "fprintf(stderr, \"Error adding L2 TCM event\\n\");")

    code.append(indentation + "if (PAPI_add_event(EventSet, PAPI_L3_TCM) != PAPI_OK)")
    code.append(indentation + "     " + "fprintf(stderr, \"Error adding L3 TCM event\\n\");")


def generate_main(numFields, gen_function, listSize, printList, code):
    
    listTypeName = "CursorTy"
    listInitializeVar = "initList"
    code.append("int main(){")

    generate_papi_init_code("   ", code)
    
    #write all function definitions
    addNewLine(code)
    code.append("   " + "IntTy listSize = " + str(listSize) + ";")
    allocateList(listInitializeVar, numFields, listTypeName, code)

    #make a copy for the list initialize variable 
    copiedInitList = generate_copy_variable(listInitializeVar, code)

    #call mkList function 
    #variableMkListOut = "mkListOut"
    #code.append("   " + listTypeName + " *mkListOut " + "=" + " mkList(" + listInitializeVar + ", listSize, " + "&" + copiedInitList + ");")
    variableMkListOut = generate_call("   ", "mkList", listTypeName, [listInitializeVar, "listSize", copiedInitList], code)

    #code.append("   " + "printList(" + variableMkListOut + ");")

    #newMemForAdd1 = "add1NewMem"
    #allocateList(newMemForAdd1, numFields, listTypeName, code)

    #generate copy for add1NewMem
    #newMemForAdd1Copy = generate_copy_variable(newMemForAdd1, code)

    code.append("   " + "FILE *file = fopen(\"output.txt\", \"w\");")

    #call add1Recursive
    callCode = []
    variableAdd1ListOut = "" 
    if gen_function == "add1RecursiveInPlace":
        copyMkListOut = generate_copy_variable(variableMkListOut, code)
        (variableAdd1ListOut, callCode) = generate_call("   ", "add1RecursiveInPlace", listTypeName, [variableMkListOut, copyMkListOut])
        time_used_var = time_call("   ", callCode, code)
        code.append("   " + "printf(\"The time taken by add1 was %f seconds.\\n\", " + time_used_var + ");")
        code.append("   " + "printf(\"Total Instructions: %lld\\n\", values[0]);")
        code.append("   " + "printf(\"L2 total cache misses: %lld\\n\", values[1]);")
        code.append("   " + "printf(\"L3 total cache misses: %lld\\n\", values[2]);")
        if printList:
            code.append("   " + "printList(" + variableAdd1ListOut + ", file" + ");")
    elif gen_function == "add1IterativeInPlace":
        (_, callCode) = generate_call("   ", "add1IterativeInPlace", "void", [variableMkListOut])
        time_used_var = time_call("   ", callCode, code)
        code.append("   " + "printf(\"The time taken by add1 was %f seconds.\\n\", " + time_used_var + ");")
        code.append("   " + "printf(\"Total Instructions: %lld\\n\", values[0]);")
        code.append("   " + "printf(\"L2 total cache misses: %lld\\n\", values[1]);")
        code.append("   " + "printf(\"L3 total cache misses: %lld\\n\", values[2]);")
        if printList:
            code.append("   " + "printList(" + variableMkListOut + ", file" + ");")
    elif gen_function == "add1IterativeOutOfPlace":
        newMemForAdd1 = "add1NewMem"
        allocateList(newMemForAdd1, numFields, listTypeName, code)
        (_, callCode) = generate_call("   ", "add1IterativeOutOfPlace", "void", [variableMkListOut, newMemForAdd1])
        time_used_var = time_call("   ", callCode, code)
        code.append("   " + "printf(\"The time taken by add1 was %f seconds.\\n\", " + time_used_var + ");")
        code.append("   " + "printf(\"Total Instructions: %lld\\n\", values[0]);")
        code.append("   " + "printf(\"L2 total cache misses: %lld\\n\", values[1]);")
        code.append("   " + "printf(\"L3 total cache misses: %lld\\n\", values[2]);")
        if printList:
            code.append("   " + "printList(" + newMemForAdd1 + ", file" + ");")
    elif gen_function == "add1RecursiveOutOfPlace":
        newMemForAdd1 = "add1NewMem"
        allocateList(newMemForAdd1, numFields, listTypeName, code)
        newMemForAdd1Copy = generate_copy_variable(newMemForAdd1, code)
        copyNewMemForAdd1Copy = generate_copy_variable(newMemForAdd1Copy, code)
        (variableAdd1ListOut, callCode) = generate_call("   ", "add1RecursiveOutOfPlace", listTypeName, [variableMkListOut, newMemForAdd1Copy, copyNewMemForAdd1Copy])
        time_used_var = time_call("   ", callCode, code)
        code.append("   " + "printf(\"The time taken by add1 was %f seconds.\\n\", " + time_used_var + ");")
        code.append("   " + "printf(\"Total Instructions: %lld\\n\", values[0]);")
        code.append("   " + "printf(\"L2 total cache misses: %lld\\n\", values[1]);")
        code.append("   " + "printf(\"L3 total cache misses: %lld\\n\", values[2]);")
        if printList:
            code.append("   " + "printList(" + variableAdd1ListOut + ", file" + ");")

    code.append("}")



if __name__ == "__main__":

    parser = argparse.ArgumentParser(description="This program generates a list with k field and autogenerates and times associated functions.\n")
    
    # Add arguments
    parser.add_argument('--k', type=int, help='The number of fields to generate in a Cons list.', required=True)
    parser.add_argument('--l', type=int, help='The number of fields to traverse.', required=True)
    parser.add_argument('--outFile', type=str, help='The name of the file to store the output to.', required=True)
    parser.add_argument('--function', type=str, choices=['add1RecursiveInPlace', 'add1IterativeInPlace', 'add1RecursiveOutOfPlace', 'add1IterativeOutOfPlace'], help='The name of the function to generate code for.', required=True)
    parser.add_argument('--listSize', type=int, help='The size of the cons list.', required=True)
    parser.add_argument('--printList', type=bool, default=False, help='Print the final cons list.')

    args = parser.parse_args()
    numFields  = args.k
    numUsedFields = args.l
    outputFile = args.outFile
    gen_function = args.function
    listSize = args.listSize 
    printList = args.printList
    
    code = []
    writeCHeaders(code)
    #generate_k_field_list_dtype(numFields, code)
    generate_k_list_build_function(numFields, code)
    generate_list_print_function(numFields, code)
    generate_add1_recursive_out_of_place(numFields, code, numUsedFields)
    generate_add1_iterative_in_place(numFields, code, numUsedFields)
    generate_add1_iterative_out_of_place(numFields, code, numUsedFields)
    generate_add1_recursive_in_place(numFields, code, numUsedFields)
    generate_main(numFields, gen_function, listSize, printList, code)
    writeCodeToFile(outputFile, code) 


