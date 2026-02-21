Rust config
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Eager promotion is enabled.
Burning is enabled.
Compaction is enabled.
INFO_TABLE: [[], [], [], [], [], [], [], [DataconInfo { scalar_bytes: 24, num_shortcut: 0, num_scalars: 3, num_packed: 0, field_tys: [] }, DataconInfo { scalar_bytes: 24, num_shortcut: 0, num_scalars: 3, num_packed: 2, field_tys: [7, 7] }]]
Initialized footer at 0x63f397116918: GibOldgenChunkFooter { reg_info: 0x63f397116940, size: 488, next: 0x0 }; GibRegionInfo {id: 0, refcount: 1, outset: {}, first_chunk_footer: GibOldgenChunkFooter { reg_info: 0x63f397116940, size: 488, next: 0x0 } }
Initialized footer at 0x63f39a333688: GibOldgenChunkFooter { reg_info: 0x63f39a3333c0, size: 488, next: 0x0 }; GibRegionInfo {id: 1, refcount: 1, outset: {}, first_chunk_footer: GibOldgenChunkFooter { reg_info: 0x63f39a3333c0, size: 488, next: 0x0 } }
Initialized footer at 0x63f3d8c54c18: GibOldgenChunkFooter { reg_info: 0x63f39a3336f0, size: 488, next: 0x0 }; GibRegionInfo {id: 2, refcount: 1, outset: {}, first_chunk_footer: GibOldgenChunkFooter { reg_info: 0x63f39a3336f0, size: 488, next: 0x0 } }

C config
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Generational GC is disabled.
Eager promotion is enabled.
Simple write barrier is disabled.
Nursery size=4194304
Max chunk size=65500
Initial chunk size=512

Number of threads: 1
Nursery info: start=0x7dd5da1ff010, end=0x7dd5da5ff010, alloc=0x7dd5da5ff010, size=4194304

itertime: 0.009652
itertime: 0.008901
itertime: 0.008984
itertime: 0.008929
itertime: 0.008953
itertime: 0.008785
itertime: 0.008944
itertime: 0.008932
itertime: 0.008907
itertime: 0.008840
itertime: 0.008831
itertime: 0.008924
itertime: 0.008872
itertime: 0.008987
itertime: 0.008625
itertime: 0.007499
itertime: 0.006273
itertime: 0.005449
itertime: 0.004769
itertime: 0.004188
ITER TIMES: [0.004188, 0.004769, 0.005449, 0.006273, 0.007499, 0.008625, 0.008785, 0.008831, 0.008840, 0.008872, 0.008901, 0.008907, 0.008924, 0.008929, 0.008932, 0.008944, 0.008953, 0.008984, 0.008987, 0.009652]
ITERS: 20
SIZE: 1
BATCHTIME: 1.622431e-01
SELFTIMED: 8.901234e-03
itertime: 0.004454
itertime: 0.003850
itertime: 0.003482
itertime: 0.003120
itertime: 0.002952
itertime: 0.002771
itertime: 0.002694
itertime: 0.002608
itertime: 0.002657
itertime: 0.002651
itertime: 0.002648
itertime: 0.002645
itertime: 0.002666
itertime: 0.002660
itertime: 0.002718
itertime: 0.002622
itertime: 0.002631
itertime: 0.002633
itertime: 0.002628
itertime: 0.002610
ITER TIMES: [0.002608, 0.002610, 0.002622, 0.002628, 0.002631, 0.002633, 0.002645, 0.002648, 0.002651, 0.002657, 0.002660, 0.002666, 0.002694, 0.002718, 0.002771, 0.002952, 0.003120, 0.003482, 0.003850, 0.004454]
ITERS: 20
SIZE: 1
BATCHTIME: 5.770045e-02
SELFTIMED: 2.660027e-03
itertime: 0.002409
itertime: 0.002450
itertime: 0.002373
itertime: 0.002402
itertime: 0.002389
itertime: 0.002379
itertime: 0.002385
itertime: 0.002390
itertime: 0.002378
itertime: 0.002371
itertime: 0.002395
itertime: 0.002411
itertime: 0.002397
itertime: 0.002396
itertime: 0.002376
itertime: 0.002409
itertime: 0.002353
itertime: 0.002358
itertime: 0.002392
itertime: 0.002393
ITER TIMES: [0.002353, 0.002358, 0.002371, 0.002373, 0.002376, 0.002378, 0.002379, 0.002385, 0.002389, 0.002390, 0.002392, 0.002393, 0.002395, 0.002396, 0.002397, 0.002402, 0.002409, 0.002409, 0.002411, 0.002450]
ITERS: 20
SIZE: 1
BATCHTIME: 4.780260e-02
SELFTIMED: 2.392418e-03
itertime: 0.002558
itertime: 0.002525
itertime: 0.002467
itertime: 0.002419
itertime: 0.002453
itertime: 0.002535
itertime: 0.002523
itertime: 0.002474
itertime: 0.002436
itertime: 0.002439
itertime: 0.002445
itertime: 0.002517
itertime: 0.002488
itertime: 0.002477
itertime: 0.002425
itertime: 0.002524
itertime: 0.002469
itertime: 0.002426
itertime: 0.002422
itertime: 0.002478
ITER TIMES: [0.002419, 0.002422, 0.002425, 0.002426, 0.002436, 0.002439, 0.002445, 0.002453, 0.002467, 0.002469, 0.002474, 0.002477, 0.002478, 0.002488, 0.002517, 0.002523, 0.002524, 0.002525, 0.002535, 0.002558]
ITERS: 20
SIZE: 1
BATCHTIME: 4.950133e-02
SELFTIMED: 2.474390e-03
itertime: 0.016710
itertime: 0.015877
itertime: 0.015679
itertime: 0.015475
itertime: 0.015446
itertime: 0.015375
itertime: 0.015117
itertime: 0.015158
itertime: 0.015646
itertime: 0.014907
itertime: 0.015143
itertime: 0.015161
itertime: 0.015552
itertime: 0.015890
itertime: 0.015579
itertime: 0.015168
itertime: 0.015517
itertime: 0.015590
itertime: 0.015364
itertime: 0.015489
ITER TIMES: [0.014907, 0.015117, 0.015143, 0.015158, 0.015161, 0.015168, 0.015364, 0.015375, 0.015446, 0.015475, 0.015489, 0.015517, 0.015552, 0.015579, 0.015590, 0.015646, 0.015679, 0.015877, 0.015890, 0.016710]
ITERS: 20
SIZE: 1
BATCHTIME: 3.098437e-01
SELFTIMED: 1.548868e-02
itertime: 0.015902
itertime: 0.015656
itertime: 0.015745
itertime: 0.015826
itertime: 0.015431
itertime: 0.015490
itertime: 0.015611
itertime: 0.015398
itertime: 0.015540
itertime: 0.015552
itertime: 0.014978
itertime: 0.015586
itertime: 0.015474
itertime: 0.015175
itertime: 0.015648
itertime: 0.015662
itertime: 0.015445
itertime: 0.015602
itertime: 0.015365
itertime: 0.015576
ITER TIMES: [0.014978, 0.015175, 0.015365, 0.015398, 0.015431, 0.015445, 0.015474, 0.015490, 0.015540, 0.015552, 0.015576, 0.015586, 0.015602, 0.015611, 0.015648, 0.015656, 0.015662, 0.015745, 0.015826, 0.015902]
ITERS: 20
SIZE: 1
BATCHTIME: 3.106633e-01
SELFTIMED: 1.557594e-02


'#(1048576 2 3145728 299593)
