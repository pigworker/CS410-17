# CS410-17
being the lecture materials and exercises for the 2017/18 session of CS410 Advanced Functional Programming at the University of Strathclyde

Strathclyders only: one minute papers and lecture videos will appear on our [Marx site](https://personal.cis.strath.ac.uk/conor.mcbride/Marx/?page=CS410).

## Installation instructions
0. Check if you're using bash
$ echo $0
1. If using bash: Add "export PATH=$HOME/.cabal/bin:$PATH" to the bottom of your .profile file if it isn't already there.
   Else if using tcsh: Add "set path = ($home/.cabal/bin $path)" to the bottom of your .cshrc file if it isn't already there. 

2. $ cabal update
3. $ cabal install alex
4. $ cabal install cpphs
5. $ cabal install happy
6. $ cabal install Agda
7. $ agda-mode setup
8. $ emacs test.agda -- You should see an Agda menu and (Agda) in the mode line.
9. $ git clone https://github.com/pigworker/CS410-17

## Lecture videos on YouTube

1. [Tuesday 19 September](https://www.youtube.com/watch?v=O4oczQry9Jw) Programs and Proofs
2. [Friday 22 September](https://www.youtube.com/watch?v=qcVZxQTouDk) more Programs and Proofs, Introducing "with"
3. [Tuesday 26 September](https://www.youtube.com/watch?v=8xFT9FPlm18) Proof by Induction
4. [Friday 29 September](https://www.youtube.com/watch?v=OZeDRtRmgkw) Sigma, Difference, Vector Take
5. [Tuesday 3 October](https://www.youtube.com/watch?v=b5salYMZoyM) How Rewrite Works
6. [Friday 6 October](https://www.youtube.com/watch?v=RW4aC_6n0yQ) A Comedy of (Entirely Non-Deliberate) Errors
7. [Tuesday 10 October](https://www.youtube.com/watch?v=2LxtHeZlaVw) "Dominoes", no really, this time
8. [Friday 13 October](https://www.youtube.com/watch?v=RCRddhYegzI) Functors
9. [Tuesday 17 October](https://www.youtube.com/watch?v=vTmYvoDrBlc) From Functors to Monads
10. [Friday 20 October](https://www.youtube.com/watch?v=2sykXdidZVA) Natural Transformations and Monads
11. [Tuesday 24 October](https://www.youtube.com/watch?v=iYegg8Rzhr4) From Monads to Input/Output
12. [Friday 27 October](https://www.youtube.com/watch?v=8WUz2HmXBqI) How to Run a Program (and come a-cropper) [bug report](https://github.com/agda/agda/issues/2821)
13. [Tuesday 31 October](https://www.youtube.com/watch?v=MwtWdiyFJtA) Monads on Indexed Sets (Ex2)
14. [Friday 3 November](https://www.youtube.com/watch?v=kX3mvyFHDDU) What is an Application?
15. [Tuesday 7 November](https://www.youtube.com/watch?v=ZCdYIEwcna0) Coinduction and Coalgebras
16. [Friday 10 November](https://www.youtube.com/watch?v=AjyUNakYHRs) Polynomial Data and Codata
17. [Tuesday 14 November](https://www.youtube.com/watch?v=E8xIJolKEAI) A Polynomial Universe
18. [Friday 17 November](https://www.youtube.com/watch?v=-3MiZ80WldY) The Zipper (Differentiating Polynomial Types)

## Other useful stuff

1. [SpaceMonads!](https://www.youtube.com/watch?v=QojLQY5H0RI) my keynote from CodeMesh 2016, on which Ex2 is based
