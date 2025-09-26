---
layout: default
---

<!-- <div> -->
<!-- <img class="centered img-70" src="static/gibbon.png"> -->
<!-- </div> -->

[Gibbon](https://github.com/iu-parfunc/gibbon/tree/master/gibbon-compiler)
is an experimental compiler that transforms high-level functional programs
to operate on _serialized data._ See the [README on GitHub][readme] to get started
with Gibbon.

[readme]: https://github.com/iu-parfunc/gibbon/blob/main/README.md

Typically, programs that process tree-like data represent trees using pointer-based
data structures in memory (one heap object per-leaf and per-node) because such a
layout is convenient to manipulate in a high-level programming language.
This is also generally distinct from the representation of the data in
serialized form on disk,
which means that a program must perform some sort or marshaling when working with serialized data.
Gibbon _unifies_ the in-memory and serialized formats, transforming recursive
functions to operate _directly_ on serialized data.

Additionally, while the pointer-based structure is efficient
for random access and shape-changing modifications, it can be inefficient
for traversals that process most or all of a tree in bulk.
The Gibbon project aims to explore optimizations of recursive tree transforms
by changing how trees are stored in memory.

Currently, the Gibbon compiler has multiple front-ends: an S-expression syntax
similar to Typed Racket, and a small subset of Haskell.


## Publications

### Peer-reviewed papers

|||
|--- |--- |
|ECOOP'17|**Compiling Tree Transforms to Operate on Packed Representations:** <br/> Michael Vollmer, Sarah Spall, Buddhika Chamith, Laith Sakka, Chaitanya Koparkar, Milind Kulkarni, Sam Tobin-Hochstadt, Ryan Newton [[PDF][ecoop17]]|
|PLDI'19|**LoCal: A Language for Programs Operating on Serialized Data:** <br/> Michael Vollmer, Chaitanya Koparkar, Mike Rainey, Laith Sakka, Milind Kulkarni, Ryan R. Newton [[PDF][pldi19]] [[extended version][local-tr]]|
|ICFP'21|**Efficient Tree-Traversals: Reconciling Parallelism and Dense Data Representations:** <br/> Chaitanya Koparkar, Mike Rainey, Michael Vollmer, Milind Kulkarni, Ryan R. Newton [[PDF][icfp21]]|
|ISMM'24|**Garbage Collection for Mostly Serialized Heaps:** <br/> Chaitanya Koparkar, Vidush Singhal, Aditya Gupta, Mike Rainey, Michael Vollmer, Artem Pelenitsyn, Sam Tobin-Hochstadt, Milind Kulkarni, Ryan R. Newton [[PDF][ismm24]]|
|ECOOP'24|**Optimizing Layout of Recursive Datatypes with Marmoset:** <br/> Vidush Singhal, Chaitanya Koparkar, Joseph Zullo, Artem Pelenitsyn, Michael Vollmer, Mike Rainey, Ryan Newton, Milind Kulkarni [[PDF][ecoop24]] [[extended version][ecoop24ext]]|

[ecoop17]: http://drops.dagstuhl.de/opus/volltexte/2017/7273/pdf/LIPIcs-ECOOP-2017-26.pdf
[pldi19]:  http://recurial.com/pldi19main.pdf
[local-tr]: ./public/pldi19ext.pdf
[icfp21]:  ./public/icfp21.pdf
[ismm24]:  ./public/ismm24.pdf
[ecoop24]: https://drops.dagstuhl.de/storage/00lipics/lipics-vol313-ecoop2024/LIPIcs.ECOOP.2024.38/LIPIcs.ECOOP.2024.38.pdf
[ecoop24ext]: https://arxiv.org/pdf/2405.17590


### Dissertations

* [A Language-based Approach to Programming with Serialized Data](https://recurial.com/thesis.pdf) by Michael Vollmer (2021)

* [Mostly-Serialized Data Structures for Parallel and General-Purpose Programming](./public/chaitanya_thesis23.pdf) by Chaitanya Koparkar (2023)

## Videos

* ECOOP 2017: [Compiling tree transforms to operate on packed representations](https://youtu.be/YDa60NpXp6Q?si=Y8TThFGqxJctw9ih) (Michael Vollmer)

* FHPC 2018: [Gibbon: A Compiler for Recursive Functions on mostly Serialized Data](https://youtu.be/E-LRy7YJu3o?si=j8yV9YqwHfQ8BxAy) (Chaitanya Koparkar)

* PLDI 2019: [LoCal: A Language for Programs Operating on Serialized Data](https://youtu.be/aDIr-D5Lx08?si=qVdKPY2uG-3_Feku) (Michael Vollmer)

* ICFP 2021: [Efficient Tree-Traversals: Reconciling Parallelism and Dense Data Representations](https://youtu.be/eeHYCq46nhE?si=xOt7ebV0EEiCHwE0) (Chaitanya Koparkar)

* ISMM 2024: [Garbage Collection for Mostly Serialized Heaps](https://youtu.be/8Glj9HUgkxo?si=UCEAwZpICHiYoXD3) (Ryan Newton)
