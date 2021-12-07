/* PiffPaff
 * Author: marti
 * Creation date: 05/12/2021
 */
MACHINE PiffPaff
    
CONSTANTS BARALHO; TRINCAS; PAUS; COPAS; OUROS; ESPADAS;

PROPERTIES BARALHO  <: 1..108
            & TRINCAS <: POW(BARALHO) //definir conjunto de trincas
            & PAUS <: BARALHO
            & COPAS <: BARALHO
            & OUROS <: BARALHO
            & ESPADAS <: BARALHO

VARIABLES deck1, deck2, monte, lixeira, jogadorDaVez ,trincasJogador1, trincasJogador2;
    
INVARIANT deck1 <: BARALHO & deck2 <: BARALHO
    & not((card(deck1) == 0 & card(deck2) == 0))
    & card(monte) < card(baralho) - 2*9 // baralho menos os 2 decks
    & card(lixeira) < card(baralho) - 2*9 // baralho menos os 2 decks
    & trincasJogador1 : NATURAL & trincasJogador1 >= 0 & trincasJogador1 <= 3
    & trincasJogador2 : NATURAL & trincasJogador2 >= 0 & trincasJogador2 <= 3
    & jogadorDaVez : NATURAL & (jogadorDaVez = 1 or jogadorDaVez = 2)
    & not(trincasJogador1 = 0 & trincasJogador2 = 0)
    & deck1 /\ deck2 = {}
    & deck1 /\ monte = {}
    & deck1 /\ lixeira = {}
    & deck2 /\ monte = {}
    & deck2 /\ lixeira = {}
    
INITIALISATION 
    trincasJogador1 := 0 ||
    trincasJogador2 := 0 ||
    deck1 := {22, 3, 9, 10, 55, 92, 7, 108, 4} ||
    deck2 := {57, 60, 100, 2, 93, 30, 40, 89, 5} ||
    monte := BARALHO / (deck1 \/ deck2) ||
    lixeira := {} ||
    jogadorDaVez := 0
    
OPERATIONS

comprarDomonte =
    PRE card(monte) > 0
    THEN
        IF (jogadorDaVez = 1) THEN
            ANY dd WHERE dd : deck1 THEN
                monte := monte \/ {dd} || deck1 := deck1 / {dd};
            END
        ELSE 
            ANY dd WHERE dd : deck2 THEN
                monte := monte \/ {dd} || deck1 := deck1 / {dd};
            END
        END
    END;
   
comprarDaLixeira =
    PRE card(lixeira) > 0
    THEN
        IF (jogadorDaVez = 1) THEN
            ANY dd WHERE dd : deck1 THEN
                lixeira := lixeira \/ {dd} || deck2 := deck2 / {dd};
            END
        ELSE 
            ANY dd WHERE dd : deck2 THEN
                lixeira := lixeira \/ {dd} || deck2 := deck2 / {dd};
            END
        END
    END;
   
abaixarTrinca = 
    PRE (jogadorDaVez = 1 & trincasJogador1 > 0) or (jogadorDaVez = 2 & trincasJogador2 > 0)
    THEN
        IF (jogadorDaVez = 1) THEN
            SELECT c1: deck1 THEN
                SELECT c2 : deck1 THEN
                    SELECT c3 : deck1 THEN
                        IF {c1, c2, c3} : TRINCAS) THEN
                            deck1 := deck1 / {c1, c2, c3} || trincasJogador1 := trincasJogador1 + 1
                        END
                        jogadorDaVez := 2
                    END
                END
            END
        ELSE
            SELECT c1: deck2 THEN
                SELECT c2 : deck2 THEN
                    SELECT c3 : deck2 THEN
                        IF {c1, c2, c3} : TRINCAS) THEN
                            deck2 := deck2 / {c1, c2, c3} || trincasJogador1 := trincasJogador1 + 1
                        END
                        jogadorDaVez := 1
                    END
                END
            END
        END    
    END; 

descartar(jj) = 
    PRE ((card(deck1) == 10 || card(deck2) == 10) 
        || (card(deck1) == 7 || card(deck2) == 7)
        || (card(deck1) == 4 || card(deck2) == 4))
    IF (jogadorDaVez == 1) THEN
        CHOICE dd : deck1
            lixeira := lixeira \/ {dd};
            deck1 := deck1 / {dd};
    ELSE 
        CHOICE dd : deck2
            lixeira := lixeira \/ {dd};
            deck1 := deck1 / {dd};
    END;
    
passarAVez = 
    IF (jogadorDaVez == 1) THEN
        jogadorDaVez := 2;
    ELSE
        jogadorDaVez := 1;
    END;

END