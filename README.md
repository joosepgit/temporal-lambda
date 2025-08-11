# Temporal Millet

Temporal Millet was implemented as part of a Master's thesis that showcases how type systems can be used to track the temporal availability of resources, and how types can be inferred for unannotated terms in the presence of temporal effects. It is a pure ML-like language, built as an extension of Millet (https://github.com/matijapretnar/millet). The concepts implemented in Temporal Millet are hugely inspired by the work of Ahman and Žajdela (https://msfp-workshop.github.io/msfp2024/submissions/ahman+%c5%beajdela.pdf).

## How to install and run Temporal Millet?

Install dependencies by

    opam install menhir vdom ocamlformat=0.27.0

and build Millet by running (tested with OCaml >= 5.1.1)

    make

and you can clean up by running

    make clean

The repository also includes automated tests that run on every master build. To run the tests locally, run

    make test

Temporal Millet, like original Millet, gives you two options to run programs:

- The first option is a web interface, accessible at `web/index.html`, which allows you to load one of the built-in examples or enter your own program, and then interactively click through all its (non-deterministic and asynchronous) reductions or introduce external interrupts. The web interface of Temporal Millet also showcases an interactive state that tracks temporal information. It is also available at <https://joosepgit.github.io/temporal-lambda/>.

- The second option is a command line executable run as

      ./cli.exe file1.mlt file2.mlt ...

  which loads all the commands in all the listed files and starts evaluating the given program, displaying all outgoing signals and the terminal configuration (if there is one). Non-deterministic reductions are chosen randomly and there is no option of introducing external interrupts. If you do not want to load the standard library, run Temporal Millet with the `--no-stdlib` option. If you want to see the variable context and state at the end of a program, run Temporal Millet with the `--debug` option.
