## Layout optimization benchmarks (Focusing on Relative ordering of Fields right now.)
* Long term goal is to show how layout affects performance, add factoring into picture + add string support + (after factoring support -> vectorization support)
* Tie everything to microservices, (social media apps for instance) + Render Tree benchmarks (Real world applications)

This is a collection of some benchmarks that show how layout affects performance.
In particular this set of benchmarks shows how the position of different fields in the data layout could potentially affect performance. 
The file Adts.hs contains the definitions of all the abstract data types and some other accompanying functions.
The file Strings.hs contains the definition of the data type String which is a Cons Int list. 
The file Tags.hs contains the definition of the data type Tags which is also a Cons Int list. 
the file Contents.hs contains the definition of the data type Content which can be an Image string or Text string. 

3 different scenarios: 

1.) Counting the length of two different Adts (Abstract data types) 
    CA (Content) (Adts) -> Content is serialized first before we serialize the next Adt. 
    AC (Adts) (Content) -> The next Adt is serialized first before we serialize any of the Content. 
    
    Here the function simply counts the length of the Adt given these 2 different data layouts. 
    
    Performance discussion... 
    
    Here the CA data layout results in slower performance that the AC layout. 
    This is because the CA layout inserts pointers to the next Adt so that it can skip over the Content (Since there is no processing done with the content) to count the length of the Adt.
    This causes the program to chases pointers to get to the end of the list. 
    On the other hand, the AC list does not have these pointers and simply traverses the Next directly since they are contiguous in memory. It does not have to chase pointers and the program exits when it sees Nil without having to deal with the content which is serialized after Nil Cell in the Adt. 
    
    Tested on Adt with number of cells = 1000000
                   size of the content = 100 elements
   
    AC
    Time for Adt: AC
    L2 Cache Misses : 305988
    L3 Cache Misses : 33032
    Instructions : 54003275
    Total Cycles : 18108744
    CPI: 0.335327
    TIMES: [0.000514, 0.000514, 0.000514, 0.000514, 0.000514, 0.000514, 0.000520, 0.000529, 0.000531]
    ITERS: 9
    SIZE: 0
    BATCHTIME: 4.665207e-03
    SELFTIMED: 5.142910e-04
    Count of Adt AC is: 1000000
    '#()
  
    CA
    Time for Adt: CA
    L2 Cache Misses : 58844120
    L3 Cache Misses : 58279137
    Instructions : 54002788
    Total Cycles : 1302125996
    CPI: 24.112199
    TIMES: [0.035460, 0.035528, 0.035551, 0.035585, 0.035706, 0.036255, 0.036775, 0.037116, 0.037521]
    ITERS: 9
    SIZE: 0
    BATCHTIME: 3.254971e-01
    SELFTIMED: 3.570562e-02
    Count of Adt CA is: 1000000
    '#()

    Speedup ~ 70x
    
    Why are the Instructions still approx. the same when measured via PAPI?
    
    AC C code:
    ...
    CursorTy tmpcur_5265 = adt_31_923_1539 + 1;
    ...
    IntTy fltAppE_1525_1543 = 1 + accumulator_32_924_1540;
    IntTy tailapp_3360 = getLengthTR(end_r_2554, tmpcur_5265, fltAppE_1525_1543);
    ...
    
    CA C code:
    ...
    CursorTy tmpcur_5890 = adt_31_923_1539 + 1;
    ...
    CursorTy tmpcur_5891 = *(CursorTy *) tmpcur_5890;
    IntTy fltAppE_1525_1543 = 1 + accumulator_32_924_1540;
    IntTy tailapp_3835 = getLengthTR(end_r_2860, tmpcur_5891, fltAppE_1525_1543);
    ...
    
    Looking at the C code it would seem like the CA layout should have more instructions due to the extra pointer de-reference.
    Assembly Code: 
    
    AC .S code: 
    The increment of the address is computed via 
    addq	$1, %rsi
    
    
    CA .S code: 
    The increment of the address is computed via
    movq	1(%rsi), %rsi
    
    Since the CISC instruction set has an instruction for loading the pointer with an offset via movq. The total number of instructions remain the same. 
    
    
    
2.) Processing the content. Comparing the performance of CA vs AC

    TODO: add some discussion here... 


3.) Processing tags when the Abstract data type has 3 fields, Tags, Content and Next Adt. 

    Here we test all the 12 permutations of the layout but and traversal order.
    
    Below are numbers for all j X k variations of the source code and data layout.
    Here j = total number of ways you can traverse the Adt, i.e, the specific order of fields you traverse. (Since the number of fields are 2 its tags first, next adt second or next adt first, tags second)
         k = total number of different layout = factorial(number of fields) = 3! = 6
    total variations = j X k = 2 X 6 = 12 variations.
    
    notation:
    t1 -> traverse tags first, next adt second
    t2 -> traverse next adt first, tags second
    d1 -> CAT -> Content first, Next Adt second, Tags third
    d2 -> CTA -> Content first, Tags second, Next Adt third
    d3 -> TAC -> Tags first, Next Adt second, Content third
    d4 -> TCA -> Tags first, Content second, Next Adt third
    d5 -> ATC -> Next Adt first, Tags second, Content third
    d6 -> ACT -> Next Adt first, Content second, Tags third
    
    Performance testing using PAPI, we measure the L2, L3 cache misses, number of Instructions and Cycles and the overall runtime.
    Each cell in the Adt has 10 tags and Content of size 2000 characters. (in the form of Text string)   
    The test makes an Adt of size 100,000 cells. 
    
    runtime table(seconds):
    
     k/j | d1         | d2        | d3        | d4        | d5          | d6          | 
      t1 | 4.592e-02  | 1.391e-02 | 7.282e-03 | 4.847e-02 | 4.362e-02   |  4.441e-02  | 
      t2 | 1.366e-02  | 5.003e-02 | 3.918e-02 | 5.026e-02 | 1.416e-02   |  4.565e-02  |
      
    L2 cache misses:
    
     k/j | d1         | d2        | d3        | d4        | d5          | d6          | 
      t1 | 2217093    | 2710350   | 1703596   | 3952795   | 2630472     |  2644843    | 
      t2 | 2496671    | 4381302   | 3370914   | 4531823   | 2704948     |  3782824    |
      
    L3 cache misses:
    
     k/j | d1         | d2        | d3        | d4        | d5          | d6          | 
      t1 | 1579791    | 2183898   | 1070878   | 3316226   | 2128599     |  2114494    | 
      t2 | 2028287    | 3906609   | 2710199   | 4050117   | 2204083     |  3201695    |
      
    Instructions:
    
     k/j | d1         | d2        | d3        | d4        | d5          | d6          | 
      t1 | 79688618   | 35908373  | 35909002  | 79984811  | 79688551    |  79688550   | 
      t2 | 35709106   | 78885177  | 79185414  | 79185175  | 35709240    |  79788900   |
      
    CPI:
    
     k/j | d1         | d2        | d3        | d4        | d5          | d6          | 
      t1 | 1.016672   | 1.251593  | 0.550825  | 1.205783  | 0.925680    |  0.952330   | 
      t2 | 1.258220   | 1.278253  | 0.725601  | 1.302915  | 1.318570    |  1.008022   |
      
      
    Speedup table(Baseline CAT layout, traversal t1):
    
    k/j  | d1         | d2        | d3        | d4        | d5          | d6          | 
      t1 | 1          | 3.30      | 6.305     | 0.947     | 1.05        |  1.03       | 
      t2 | 3.36       | 0.917     | 1.17      | 0.913     | 3.24        |  1.01       |
      
    CopyPacked's used:
    
    k/j  | d1         | d2        | d3        | d4        | d5          | d6         | 
      t1 | 1          | 0         | 0         | 2         | 1           |  2         | 
      t2 | 0          | 1         | 1         | 2         | 0           |  2         |
    
    

   ### MACHINE SPECIFICATIONS (Tested on a machine where PAPI support was available, newer machines not supported by PAPI yet.):
   ``` 
   Architecture:                    x86_64
   CPU op-mode(s):                  32-bit, 64-bit
   Byte Order:                      Little Endian
   Address sizes:                   39 bits physical, 48 bits virtual
   CPU(s):                          12
   On-line CPU(s) list:             0-11
   Thread(s) per core:              2
   Core(s) per socket:              6
   Socket(s):                       1
   NUMA node(s):                    1
   Vendor ID:                       GenuineIntel
   CPU family:                      6
   Model:                           158
   Model name:                      Intel(R) Core(TM) i7-8750H CPU @ 2.20GHz
   Stepping:                        10
   CPU MHz:                         2200.000
   CPU max MHz:                     4100.0000
   CPU min MHz:                     800.0000
   BogoMIPS:                        4399.99
   Virtualization:                  VT-x
   L1d cache:                       192 KiB
   L1i cache:                       192 KiB
   L2 cache:                        1.5 MiB
   L3 cache:                        9 MiB
   NUMA node0 CPU(s):               0-11
   ``` 
