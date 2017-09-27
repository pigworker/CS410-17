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

1. [Tuesday 19 September](https://www.youtube.com/watch?v=O4oczQry9Jw)
2. [Friday 22 September](https://www.youtube.com/watch?v=qcVZxQTouDk)
3. [Tuesday 26 September](https://www.youtube.com/watch?v=8xFT9FPlm18)
