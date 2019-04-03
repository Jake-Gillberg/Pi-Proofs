-- Definition 1.1.1
data LowerCaseLetter = A | B | C | D | E | F | G | H | I | J | K | L | M
                     | N | O | P | Q | R | S | T | U | V | W | X | Y | Z

data Name = LetterToName LowerCaseLetter
          | LettersToName LowerCaseLetter Name

data Prefix = Output Name Name
            | Input Name Name
            | Unobservable
            | Match Name Name Prefix

mutual
  data Process = SummationToProcess Summation
               | Composition Process Process
               | Restriction Name Process
               | Replication Process

  data Summation = Inaction
                 | Prefixed Prefix Process
                 | Sum Summation Summation
