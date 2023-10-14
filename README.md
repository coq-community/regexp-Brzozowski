<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Regexp Brzozowski

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]
[![DOI][doi-shield]][doi-link]

[docker-action-shield]: https://github.com/coq-community/regexp-Brzozowski/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/regexp-Brzozowski/actions?query=workflow:"Docker%20CI"

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users


[doi-shield]: https://zenodo.org/badge/DOI/10.1007/978-3-642-25379-9_11.svg
[doi-link]: https://doi.org/10.1007/978-3-642-25379-9_11

Coq library that formalizes decision procedures for regular
expression equivalence, using the Mathematical Components
library. The formalization builds on Brzozowski's derivatives
of regular expressions for correctness.

## Meta

- Author(s):
  - Thierry Coquand (initial)
  - Vincent Siles (initial)
- Coq-community maintainer(s):
  - Anton Trunov ([**@anton-trunov**](https://github.com/anton-trunov))
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.11 to 8.18
- Additional dependencies:
  - [MathComp](https://math-comp.github.io) 1.13.0 to 1.17.0 (`ssreflect` suffices)
  - [RegLang](https://github.com/coq-community/reglang) 1.1.3
- Coq namespace: `RegexpBrzozowski`
- Related publication(s):
  - [A Decision Procedure for Regular Expression Equivalence in Type Theory](https://link.springer.com/chapter/10.1007%2F978-3-642-25379-9_11) doi:[10.1007/978-3-642-25379-9_11](https://doi.org/10.1007/978-3-642-25379-9_11)

## Building and installation instructions

The easiest way to install the latest released version of Regexp Brzozowski
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-regexp-brzozowski
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/regexp-Brzozowski.git
cd regexp-Brzozowski
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Documentation

The [paper](https://link.springer.com/chapter/10.1007%2F978-3-642-25379-9_11) on the
formalization was written at Chalmers, in the ForMath Project. More information about
the project and its achievements is available on the Chalmers website:
- http://wiki.portal.chalmers.se/cse/pmwiki.php/ForMath
- http://wiki.portal.chalmers.se/cse/pmwiki.php/ForMath/PapersAndSlides

Overview of the Coq files:
- `glue.v`: Basic definitions and lemmas.
- `regexp.v`: Description and properties of regular expressions.
- `gfinset.v`: Alternative definition of finite sets.
- `finite_der.v`: The main proof that the set of derivatives of a regular
  expression is finite. The proof uses an abstract notion of similarity
  with the Brzozowski requirements.
- `equiv.v`: Description of the equivalence procedure and proof of its correctness.
  In case of non-equivalence, we also produce a witness which is recognized by the
  first language but not by the second.
- `sim1.v`: Naive implementation of similarity checking (by double inclusion), with
  only Brzozowski simplifications.
- `sim2.v`: More efficient implementation of similarity checking (with a "compilation"
  of regular expressions) which implements many more simplifications.
- `ex.v`: A few test cases which allow comparing the decision procedures in `sim1.v`
  and `sim2.v` inside Coq.
