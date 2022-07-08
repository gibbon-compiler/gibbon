This is a collection of some benchmarks that show how layout affects performance.
In particular this set of benchmarks shows how the position of different fields in the data layout could potentially affect performance. 
The file Adts.hs contains the definitions of all the abstract data types and some other accompanying functions.
The file Strings.hs contains the definition of the data type String which is a Cons Int list. 
The file Tags.hs contains the definition of the data type Tags which is also a Cons Int list. 
the file Contents.hs contains the definition of the data type Content which can be an Image string or Text string. 

3 different senarios: 

1.) Counting the length of two different Adts (Abstract data types) 
    CA (Content) (Adts) -> Content is serialzed first before we serialize the next Adt. 
    AC (Adts) (Content) -> The next Adt is serialized first before we serialize any of the Content. 
    
    Here the fuction simply counts the length of the Adt given these 2 different data layouts. 
    
    Performance disscussion... 
    
    Here the CA data layout results in slower performance that the AC layout. 
    This is because the CA layout inserts pointers to the next Adt so that it can quickly skip over the Content and to count the length of the Adt. This causes the program to chases pointes to get to the end of the list. 
    On the other hand, the AC list does not have these pointers and simply traverses the Next directly since they are contigous in memory. This way it does not have to chase pointes and the program exits when it sees Nil without having to deal with the content.
   
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
    
    
2.) Processing the content. Comparing the performance of CA vs AC

    TODO: add some discussion here... 


3.) Processing tags when the Abstract data type has 3 fields, Tags, Content and Next Adt. 

    Here we test all the 6 permutations of the layout but specifically discuss the performance of the TAC and CAT layouts. 
    TAC -> Tags, Adt next and then Content is serialized. 
    CAT -> Content, next Adt and then Tags are serialized. 
    
    TAC is faster than CAT. The function adds a set value to all the tags (emulating a traversal over all the tags)
    TODO: Add more explanation here...
    
    Performance testing using PAPI, we measure the L2, L3 cache misses, number of Instructions and Cycles. 
    
    The test makes TAC and CAT abstract data layout of size 10,000 cells. 
    Each cell has a list of 10 tags and Content of size 2000 characters. (in the form of Text string)   
    
    TAC
    L2 Cache Misses : 15208512
    L3 Cache Misses : 9449631
    Instructions : 323168259
    Total Cycles : 179453423
    CPI: 0.555294
    TIMES: [0.007453, 0.007480, 0.007590, 0.007745, 0.007779, 0.007794, 0.007797, 0.007896, 0.008106]
    ITERS: 9
    SIZE: 0
    BATCHTIME: 6.963932e-02
    SELFTIMED: 7.778918e-03
    '#()
    
    
    CAT
    L2 Cache Misses : 20032647
    L3 Cache Misses : 14033895
    Instructions : 717124396
    Total Cycles : 742859227
    CPI: 1.035886
    TIMES: [0.047035, 0.047063, 0.047065, 0.047089, 0.047130, 0.047576, 0.047665, 0.048015, 0.048623]
    ITERS: 9
    SIZE: 0
    BATCHTIME: 4.272612e-01
    SELFTIMED: 4.712992e-02
    '#()
    
    TAC has less L2 and L3 cache misses, lesser instructions and cycles and consequently a lower runtime. 

    Speedup ~ 6x.

   MACHINE SPECIFICATIONS: 
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
Vulnerability Itlb multihit:     KVM: Mitigation: VMX disabled
Vulnerability L1tf:              Mitigation; PTE Inversion; VMX conditional cache flushes, SMT vulnerable
Vulnerability Mds:               Mitigation; Clear CPU buffers; SMT vulnerable
Vulnerability Meltdown:          Mitigation; PTI
Vulnerability Spec store bypass: Mitigation; Speculative Store Bypass disabled via prctl and seccomp
Vulnerability Spectre v1:        Mitigation; usercopy/swapgs barriers and __user pointer sanitization
Vulnerability Spectre v2:        Mitigation; Retpolines, IBPB conditional, IBRS_FW, STIBP conditional, RSB filling
Vulnerability Srbds:             Mitigation; Microcode
Vulnerability Tsx async abort:   Not affected
Flags:                           fpu vme de pse tsc msr pae mce cx8 apic sep mtrr pge mca cmov pat pse36 clflush dts acpi mmx fxsr sse sse2 ss ht tm pbe syscall nx pdpe1gb rdtscp lm constant_tsc art arch_perfmon pebs bts rep_good nopl xtopology nonstop_tsc cpuid
                                  aperfmperf pni pclmulqdq dtes64 monitor ds_cpl vmx est tm2 ssse3 sdbg fma cx16 xtpr pdcm pcid sse4_1 sse4_2 x2apic movbe popcnt tsc_deadline_timer aes xsave avx f16c rdrand lahf_lm abm 3dnowprefetch cpuid_fault epb invpcid_singl
                                 e pti ssbd ibrs ibpb stibp tpr_shadow vnmi flexpriority ept vpid ept_ad fsgsbase tsc_adjust sgx bmi1 avx2 smep bmi2 erms invpcid mpx rdseed adx smap clflushopt intel_pt xsaveopt xsavec xgetbv1 xsaves dtherm ida arat pln pts hwp h
                                 wp_notify hwp_act_window hwp_epp sgx_lc md_clear flush_l1d
 
    
