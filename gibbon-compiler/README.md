A prototype compiler for the Gibbon language, a simple functional
language for writing tree traversals.

The main feature of the Gibbon compiler is that it transforms programs
to automatically operate over serialized versions of algebraic data
types, rather than over their natural, pointer-based representations.


Further reading
---------------

Aside from looking at the code
[documentation](http://iu-parfunc.github.io/gibbon/haddocks/),
you may want to read about the basic intermediate languages that the compiler uses.

 * [L0](src/Gibbon/L0)
 * [L1](src/Gibbon/L1)
 * [L2](src/Gibbon/L2)
 * [L3](src/Gibbon/L3)
 * [L4](src/Gibbon/L4)

You can also read the
[ECOOP'17 paper](http://drops.dagstuhl.de/opus/volltexte/2017/7273/pdf/LIPIcs-ECOOP-2017-26.pdf),
however it is already substantially out of date (as of 2017.08.01).

For developers: Coding Style
----------------------------

For this project, please follow the coding style described here:

https://github.com/rrnewton/haskell-style-guide/blob/master/RRN_style_guide.md
