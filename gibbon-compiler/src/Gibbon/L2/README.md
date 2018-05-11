The L2 Language
===============

The L2 language deals with locations and regions.  Locations don't
*necessarily* have runtime representations in this language, but they
could.  Well-typed L2 programs bind all the locations that are
used with LetLoc forms, or bindings inside case expressions.

L2 also supports multi-valued returns with extra location values
in addition to a single regular value.  This supports the output of
the RouteEnds pass.

