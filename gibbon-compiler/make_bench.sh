# OPT_LEVEL=-O3
OPT_LEVEL="-O0 -g"

gcc -std=gnu11  $OPT_LEVEL  -flto  -o $GIBBONDIR/gibbon-compiler/examples/gc/Reverse_1.exe -I$GIBBONDIR/gibbon-rts/build -L$GIBBONDIR/gibbon-rts/build -Wl,-rpath=$GIBBONDIR/gibbon-rts/build $GIBBONDIR/gibbon-compiler/examples/gc/Reverse_1.c $GIBBONDIR/gibbon-rts/build/gibbon_rts.o -lm  -lgibbon_rts_ng

# gcc -std=gnu11  -O0 -g -flto  -o $GIBBONDIR/gibbon-compiler/examples/gc/Coins.exe -I$GIBBONDIR/gibbon-rts/build -L$GIBBONDIR/gibbon-rts/build -Wl,-rpath=$GIBBONDIR/gibbon-rts/build $GIBBONDIR/gibbon-compiler/examples/gc/Coins.c $GIBBONDIR/gibbon-rts/build/gibbon_rts.o -lm  -lgibbon_rts_ng

gcc -std=gnu11  $OPT_LEVEL  -flto  -o $GIBBONDIR/gibbon-compiler/examples/gc/TreeUpdate_1.exe -I$GIBBONDIR/gibbon-rts/build -L$GIBBONDIR/gibbon-rts/build -Wl,-rpath=$GIBBONDIR/gibbon-rts/build $GIBBONDIR/gibbon-compiler/examples/gc/TreeUpdate_1.c $GIBBONDIR/gibbon-rts/build/gibbon_rts.o -lm  -lgibbon_rts_ng
