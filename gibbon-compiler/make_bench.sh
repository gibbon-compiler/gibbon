OPT_LEVEL="-O3"
# OPT_LEVEL="-O0 -g"

# CFLAGS="-D_GIBBON_SIMPLE_WRITE_BARRIER=1"
CFLAGS=""

gcc -std=gnu11  $OPT_LEVEL  $CFLAGS  -flto  -o $GIBBONDIR/gibbon-compiler/examples/gc/Reverse_1.exe -I$GIBBONDIR/gibbon-rts/build -L$GIBBONDIR/gibbon-rts/build -Wl,-rpath=$GIBBONDIR/gibbon-rts/build $GIBBONDIR/gibbon-compiler/examples/gc/Reverse_1.c $GIBBONDIR/gibbon-rts/build/gibbon_rts.o -lm  -lgibbon_rts_ng

gcc -std=gnu11  $OPT_LEVEL  $CFLAGS  -flto  -o $GIBBONDIR/gibbon-compiler/examples/gc/TreeUpdate_1.exe -I$GIBBONDIR/gibbon-rts/build -L$GIBBONDIR/gibbon-rts/build -Wl,-rpath=$GIBBONDIR/gibbon-rts/build $GIBBONDIR/gibbon-compiler/examples/gc/TreeUpdate_1.c $GIBBONDIR/gibbon-rts/build/gibbon_rts.o -lm  -lgibbon_rts_ng

gcc -std=gnu11  $OPT_LEVEL  $CFLAGS -flto  -o $GIBBONDIR/gibbon-compiler/examples/gc/Coins_1.exe -I$GIBBONDIR/gibbon-rts/build -L$GIBBONDIR/gibbon-rts/build -Wl,-rpath=$GIBBONDIR/gibbon-rts/build $GIBBONDIR/gibbon-compiler/examples/gc/Coins_1.c $GIBBONDIR/gibbon-rts/build/gibbon_rts.o -lm  -lgibbon_rts_ng

gcc -std=gnu11  $OPT_LEVEL  $CFLAGS -flto  -o $GIBBONDIR/gibbon-compiler/examples/gc/Lcss_1.exe -I$GIBBONDIR/gibbon-rts/build -L$GIBBONDIR/gibbon-rts/build -Wl,-rpath=$GIBBONDIR/gibbon-rts/build $GIBBONDIR/gibbon-compiler/examples/gc/Lcss_1.c $GIBBONDIR/gibbon-rts/build/gibbon_rts.o -lm  -lgibbon_rts_ng

gcc -std=gnu11  $OPT_LEVEL $CFLAGS  -flto  -o $GIBBONDIR/gibbon-compiler/examples/gc/TreeUpdate_2.exe -I$GIBBONDIR/gibbon-rts/build -L$GIBBONDIR/gibbon-rts/build -Wl,-rpath=$GIBBONDIR/gibbon-rts/build $GIBBONDIR/gibbon-compiler/examples/gc/TreeUpdate_2.c $GIBBONDIR/gibbon-rts/build/gibbon_rts.o -lm  -lgibbon_rts_ng

gcc -std=gnu11  $OPT_LEVEL  $CFLAGS  -flto  -o $GIBBONDIR/gibbon-compiler/examples/gc/Power_1.exe -I$GIBBONDIR/gibbon-rts/build -L$GIBBONDIR/gibbon-rts/build -Wl,-rpath=$GIBBONDIR/gibbon-rts/build $GIBBONDIR/gibbon-compiler/examples/gc/Power_1.c $GIBBONDIR/gibbon-rts/build/gibbon_rts.o -lm  -lgibbon_rts_ng

gcc -std=gnu11  $OPT_LEVEL  $CFLAGS  -flto  -o $GIBBONDIR/gibbon-compiler/examples/gc/Benchrunner_1.exe -I$GIBBONDIR/gibbon-rts/build -L$GIBBONDIR/gibbon-rts/build -Wl,-rpath=$GIBBONDIR/gibbon-rts/build $GIBBONDIR/gibbon-compiler/examples/gc/Benchrunner_1.c $GIBBONDIR/gibbon-rts/build/gibbon_rts.o -lm  -lgibbon_rts_ng

gcc -std=gnu11  $OPT_LEVEL  $CFLAGS  -flto  -o $GIBBONDIR/gibbon-compiler/examples/gc/Benchrunner_master_1.exe $GIBBONDIR/gibbon-compiler/examples/gc/Benchrunner_master_1.c -lm
