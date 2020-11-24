Classical ML
---

from https://www.cs.cmu.edu/afs/cs/project/ai-repository/ai/areas/reasonng/atp/systems/nuprl/0.html

This is the ML implementation striped from Nuprl3, with capabilities on manipulating Nuprl proof
objects disabled.

To use it, you need an ANSI complaint CL with ASDF.

`doc/` release notice and documentations

`ml/` ML tactics library, for reference

`sys/` The source for Nuprl and ML compiler

## start the system

```
CL-USER> (load "sys/nuprl.asd")
CL-USER> (asdf:load-system "nuprl")
;; now the base system has been loaded
CL-USER> (in-package "NUPRL")
NUPRL> (setup)
Cambridge ML modified for PRL, version (4 . 3)

% have fun %
% to exit from ML, try ^D, this might not work inside SLIME/Sly %
```

