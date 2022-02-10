# Building Off-Policy Evaluation Theories

HOL requires Poly/ML to run.  This can be obtained from http://polyml.org.  On Macs, it can be installed with `brew`, and on Linux with `apt-get` it can be installed this way also (the package name is `polyml`).

We require a specific version of HOL:

    git clone git@github.com:HOL-Theorem-Prover/HOL.git
    cd HOL
    git checkout 6ad5e919416a5bf9d
    poly < tools/smart-configure.sml
    bin/build

When HOL is built, the attached scripts can be built by running

    <HOLDIR>/bin/Holmake

in this directory.  The various `xTheory.sig` files contain pretty-printed  presentations of all the theorems that have been proved.

## Manifest

There are four script files:

-   `trivialScript.sml`: various auxiliary results
-   `hoeffdingScript.sml`: the proofs of Hoeffding’s lemma and inequality as per §3.1 of the paper
-   `pispaceScript.sml`: constructing product measure spaces
-   `opeScript.sml`: all other results. For example, the paper’s final result is `data_return_ci` at the bottom of this file.


