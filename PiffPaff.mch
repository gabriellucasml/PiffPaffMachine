MACHINE           PiffPaff         

SETS              BARALHO

CONSTANTS         trincas, espadas, paus, ouros, copas, vazio

PROPERTIES        espadas : 0..25   >-> BARALHO
                  & paus  : 26..51  >-> BARALHO
                  & ouros : 52..77  >-> BARALHO
                  & copas : 78..103 >-> BARALHO
                  & vazio : {-1}    >-> BARALHO
                  & card(BARALHO) = 105
                  & trincas : POW(BARALHO)

VARIABLES         deck1, deck2, monte, lixeira, mesa, jogadorDaVez, vencedor, lock

INVARIANT         deck1 :   -1..8 --> BARALHO       
                  & deck2 :  -1..8 --> BARALHO
                  & monte : -1..103 --> BARALHO
                  & mesa : -1..103 --> BARALHO
                  & lixeira : -1..103 --> BARALHO
                  & jogadorDaVez : NATURAL & (jogadorDaVez = 1 or jogadorDaVez = 2)
                  & card(lixeira) = 104
                  & card(monte) = 104
                  & vencedor : {0, 1, 2}
                  & lock : BOOL   
                  /*
                  & !(xx,yy,zz).((xx : NAT & yy : NAT & zz: NAT & {xx, yy, zz} : trincas) => 
                          (xx mod 13 = yy mod 13 
                           & xx mod 13 = zz mod 13 
                           & yy mod 13 = zz mod 13 
                           & (not(xx : espadas & yy : espadas))
                           & (not(xx : espadas & zz : espadas))
                           & (not(yy : espadas & zz : espadas))
                           & (not(xx : paus & yy : paus))
                           & (not(xx : paus & zz : paus))
                           & (not(yy : paus & zz : paus))
                           & (not(xx : ouros & yy : ouros))
                           & (not(xx : ouros & zz : ouros))
                           & (not(yy : ouros & zz : ouros))
                           & (not(xx : copas & yy : copas))
                           & (not(xx : copas & zz : copas))
                           & (not(yy : copas & zz : copas))
                          ) or ((((xx mod 13) + 1 = yy mod 13  & (yy mod 13) + 1 = zz mod 13) or // x < y < z
                                ((xx mod 13) + 1 = zz mod 13  & (zz mod 13) + 1 = yy mod 13) or // x < z < y
                                ((yy mod 13) + 1 = xx mod 13  & (xx mod 13) + 1 = zz mod 13) or // y < x < z
                                ((yy mod 13) + 1 = zz mod 13  & (zz mod 13) + 1 = xx mod 13) or // y < z < x
                                ((zz mod 13) + 1 = xx mod 13  & (xx mod 13) + 1 = yy mod 13) or // z < x < y
                                ((zz mod 13) + 1 = yy mod 13  & (yy mod 13) + 1 = xx mod 13)) // z < y < x
                                & ((xx : espadas & yy : espadas & zz : espadas) or
                                   (xx : paus & yy : paus & zz : paus) or
                                   (xx : ouros & yy : ouros & zz : ouros) or
                                   (xx : copas & yy : copas & zz : copas))))
                                
                  */
                  
INITIALISATION    deck1 := {0,1,2,3,4,5,6,7,8,9} * BARALHO
                  || deck2 := {0,1,2,3,4,5,6,7,8,9} * BARALHO
                  || monte := {0,1,2,3,4,5,6,7,8,9} * BARALHO
                  || lixeira := {0,1,2,3,4,5,6,7,8,9} * BARALHO
                  || mesa := {0,1,2,3,4,5,6,7,8,9} * BARALHO
                  || jogadorDaVez := 1
                  || vencedor := 0
                  || lock := FALSE
 
 
OPERATIONS

comprarDoMonte(cc) =
    PRE card(monte|>>{monte(-1)}) > 0 & lock = FALSE & cc = 0
    THEN
        IF (jogadorDaVez = 1) THEN
            deck1(-1) := monte(cc)                      
        ELSE 
            deck2(-1) := monte(cc) 
        END ||
        monte(cc) := vazio(-1) ||
        lock := TRUE 
    END;
    
comprarDaLixeira(cc) =
    PRE card(lixeira|>>{lixeira(-1)}) > 0 & lock = FALSE & cc = 0
    THEN
        IF (jogadorDaVez = 1) THEN
            deck1(-1) := lixeira(cc)
        ELSE 
            deck2(-1) := lixeira(cc) 
        END ||
        lixeira(cc) := vazio(-1) ||
        lock := TRUE
    END;
   

abaixarTrinca(c1, c2, c3) = 
    PRE c1 : NAT & c2 : NAT & c3 : NAT & 
        c1 /= c2 & c2 /= c3 & c1 /= c3 &
        c1 < 8 & c2 < 8 & c3 < 8 &
        c1 >= 0 & c2 >= 0 & c3 >= 0
    THEN
        IF (jogadorDaVez = 1) THEN
            IF ({deck1(c1),deck1(c2),deck1(c3)} : trincas) THEN
                mesa := mesa <+ {card(mesa |>> {mesa(-1)}) |-> deck1(c1), 
                            (card(mesa |>> {mesa(-1)}) + 1) |-> deck1(c2),
                            (card(mesa |>> {mesa(-1)}) + 2) |-> deck1(c3)} || 
                deck1 := deck1 <+ {c1 |-> deck1(-1), c2 |-> deck1(-1), c3 |-> deck1(-1)} ||
                jogadorDaVez := 2 ||
                IF(card(deck1 |>>{deck1(-1)}) = 0) THEN
                    vencedor := 1
                END
            END
        ELSE      
            IF ({deck2(c1)}\/{deck2(c2)}\/{deck2(c3)} : trincas) THEN
                mesa := mesa <+ {card(mesa |>> {mesa(-1)}) |-> deck2(c1), 
                            (card(mesa |>> {mesa(-1)}) + 1) |-> deck2(c2),
                            (card(mesa |>> {mesa(-1)}) + 2) |-> deck2(c3)} || 
                deck2 := deck2 <+ {c1 |-> deck2(-1), c2 |-> deck2(-1), c3 |-> deck2(-1)} ||
                jogadorDaVez := 2 ||
                IF(card(deck2 |>>{deck2(-1)}) = 0) THEN
                    vencedor := 2
                END
            END
        END    
    END; 


descartar(cc) = 
    PRE lock = TRUE  & cc : NAT & cc >= 0 & cc < 9
    THEN
        IF (jogadorDaVez = 1) THEN
            lixeira(card(lixeira |>>{lixeira(-1)})) := deck1(cc) ||
            deck1(cc) := vazio(-1) || 
            lock := FALSE ||
            jogadorDaVez := 2
        ELSE 
            lixeira(card(lixeira |>>{lixeira(-1)})) := deck2(cc) ||
            deck2(cc) := vazio(-1) || 
            lock := FALSE ||
            jogadorDaVez := 1
        END
    END;
    
passarAVez = 
    PRE lock = FALSE
    THEN
        IF (jogadorDaVez = 1) THEN
            jogadorDaVez := 2
        ELSE
            jogadorDaVez := 1
        END
    END
END

