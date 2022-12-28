# Principio di sostituzione

Secondo il principio _open-closed_ un modulo (che in Java coincide con una classe) dovrebbe essere _chiuso_ rispetto alla modifica ed _aperto_ rispetto all'estensione.
Cioè se vogliamo arricchire il comportamento di un certo modulo, non possiamo modificarne la specifica, bensì dobbiamo estenderlo con un sottomodulo che aggiunge nuove funzionalità.

In Java, per realizzare l'estensione ricorriamo al meccanismo di ereditarietà.
Dobbiamo però fare attenzione: **NON** tutte le sottoclassi ottenute tramite ereditarietà realizzano un'estensione della superclasse. In particolare, perchè una sottoclasse `B` **estenda** la corrispondente superclasse `A`, gli oggetti di `B` devono essere _sostituibili_ a quelli di `A`; nel senso che gli oggetti di `B` possono essere utilizzati da un utente come oggetti della classe `A`, senza notare alcuna differenza.

Per formalizzare questo concetto di _sostituibilità_, introduciamo il **principio di sostituzione di Liskov**: _"Tutti gli oggetti della sottoclasse devono soddisfare il contratto della superclasse"_, ma il contratto può essere esteso per coprire ulteriori casi.

Consideriamo l'esempio `InsiemeDiInteri` introdotto nel paragrafo _Esempio_ nel capitolo _JML_.
Aggiungiamo alla classe `InsiemeDiInteri` un `Iterator` che permette di iterare sugli elementi dell'insieme senza garantire un ordine preciso (scriviamo solo la specifica):
```java
public class InsiemeDiInteri {
  ...
  //@ ensures (* restituisce un iteratore che
  //@   itera su tutti e soli gli elementi
  //@   dell'insieme, ognuno visitato una        
  //@   volta, in un ordine qualsiasi *);
  public Iterator<Integer> iterator();
  ...
}
```

Supponiamo che un utente di `InsiemeDiInteri` voglia implementare il metodo `traccia` che calcola la somma di tutti gli elementi appartenenti all'insieme (ciascuno considerato nella somma una ed una sola volta):
```java
public static int traccia(InsiemeDiInteri s) {
  int somma = 0;
  for (Iterator<Integer> iter = s.iterator();
    iter.hasNext(); ) {
    somma += iter.next();
  }
  return somma;
}
```
Consideriamo le seguenti sottoclassi che ereditano da `InsiemeDiInteri`:
```java
public class InsiemeDiInteriIteratorOrdinato
  extends InsiemeDiInteri {
  @Override
  //@ ensures (* restituisce un iteratore che
  //@   itera su tutti e soli gli elementi
  //@   dell'insieme, ognuno visitato una        
  //@   volta, in ordine crescente *);
  public Iterator<Integer> iterator();
}
```
e
```java
public class InsiemeDiInteriIteratorPositivi
  extends InsiemeDiInteri {
  @Override
  //@ ensures (* restituisce un iteratore che
  //@   itera su tutti e soli gli elementi
  //@   positivi dell'insieme, ognuno visitato
  //@   una volta,
  //@   in un ordine qualsiasi *);
  public Iterator<Integer> iterator();
}
```

Il metodo `traccia` continua a funzionare sugli oggetti della classe `InsiemeDiInteriIteratorOrdinato` (dato che vale la proprietà commutativa della somma). In particolare la ridefinizione di `iterator` di questa sottoclasse continua a soddisfare il contratto della superclasse (dato che la superclasse ammette che gli elementi vengano visitati in un ordine **qualsiasi**).
Al contrario quando richiamiamo `traccia` con un oggetto della classe `InsiemeDiInteriIteratorPositivi`, ciò che viene calcolato è la somma dei soli elementi positivi dell'insieme e non la _traccia_ dell'insieme. Infatti la ridefinizione di `iterator` in `InsiemeDiInteriIteratorPositivi` viola il contratto della superclasse: **NON** itera su tutti e soli gli elementi dell'insieme, ma solo sui positivi.
In conclusione `InsiemeDiInteriIteratorOrdinato` soddisfa il principio di sostituzione, `InsiemeDiInteriIteratorPositivi` **NO**.

## Regole per soddisfare il principio di sostituzione

Per assicurarci che il contratto di una sottoclasse sia compatibile con quello della superclasse (e quindi che la sottoclasse soddisfi il principio di sostituzione) è sufficiente verificare che valgano le tre _regole_ che seguono:
- _signature rule_: una sottoclasse deve disporre di tutti i metodi della superclasse e le firme dei metodi della sottoclasse devono essere **compatibili** con quelle dei metodi della superclasse
- _methods rule_: le chiamate ad un metodo della <br>sottoclasse si devono "comportare" come le chiamate <br>al metodo corrispondente della superclasse
- _property rule_: una sottoclasse deve preservare tutte le proprietà astratte (vedi capitolo sul JML) degli oggetti della superclasse

La _signature rule_ garantisce che la sintassi con cui operiamo sulla sottoclasse sia compatibile con la sintassi della superclasse.
La _methods rule_ garantisce che il contratto (inteso come la specifica) di ciascun metodo _ereditato_ sia compatibile con il contratto del metodo _originale_. In particolare un'estensione si dice **pura** se non cambia la specifica (aggiunge solo dei metodi).
La _property rule_ garantisce che la specifica della sottoclasse nella sua interezza sia compatibile con quella della classe originale.

### _Signature rule_

La _signature rule_ è verificabile **staticamente** dal compilatore di Java.

---

In particolare la _signature rule_ "implementata" in Java è: una sottoclasse deve avere tutti i metodi della superclasse e la firma dei metodi della sottoclasse deve essere **identica** a quella dei metodi corrispondenti della superclasse. Un metodo della sottoclasse può però avere meno eccezioni di quello della superclasse (ricordiamo che in Java la firma di un metodo è costituita dal suo nome e dalla lista dei parametri, ma non include il tipo restituito, quindi non possiamo dichiarare nella stessa classe due metodi che hanno lo stesso nome e la stessa lista di parametri anche se restituiscono un tipo diverso).
Notiamo che la _signature rule_ in Java è **più restrittiva** di quella enunciata nel caso generale, infatti esistono metodi che hanno firma **compatibile** ma **NON identica**. Per dimostrarlo occorre introdurre i concetti di controvarianza e covarianza.

#### Controvarianza e covarianza

L'esempio che segue non è valido in Java, dato che ci serve per illustrare i concetti di **controvarianza** e **covarianza** che non sono entrambi validi nel linguaggio.
Consideriamo una superclasse `A` che definisce il metodo `f : PA -> RA` (dove `PA` è la classe dei parametri di `f` e `RA` è la classe degli oggetti restituiti da `f`).
Sia `D` una sottoclasse di `A` che **ridefinisce** il metodo `f` come `f : PD -> RD`.
Consideriamo uno snippet di codice che utilizza un oggetto della classe `A` (dato che non facciamo riferimento ad un linguaggio in particolare useremo una sintassi inventata):
```
method void usaA(A a) {
  ...
  RA rA = a.f(pA);
  ...
}
```
Supponiamo di passare come parametro in `usaA` un oggetto `d` della classe `D`.
Perchè la _signature rule_ sia verificata, l'oggetto `pA`, che ha tipo dinamico `PA` deve poter essere accettato come parametro anche da `D.f`, che si aspetta un parametro di tipo `PD`. Quindi la classe `PD` può coincidere con la classe `PA` o può essere un **supertipo** della classe `PA`. Il fatto che se `PD` è una superclasse di `PA`, la _signature rule_ è ancora soddisfatta, si dice **controvarianza dei parametri di input**. La controvarianza dei parametri di input **NON** è supportata in Java, dove, per fare un override, è necessario che `PD` **coincida** con `PA`.

Consideriamo ora il valore restituito da `a.f` (sempre nel caso in cui abbiamo passato ad `usaA` un oggetto `d` della classe `D`).
`a.f` restituirà un oggetto della classe `RD`, che, perché la _signature rule_ sia verificata, deve poter essere assegnato ad un oggetto di tipo `RA` come l'utente si aspetta. Quindi `RD` può coincidere con `RA` oppure può essere una sottoclasse di `RA`. Il fatto che se `RD` è una sottoclasse di `RA`, la _signature rule_ è ancora soddisfatta, si dice **covarianza dei risultati**. La covarianza dei risultati è ammissibile in Java a partire da Java 5.

### _Methods rule_

Perché la chiamata di un metodo di una sottoclasse abbia lo stesso effetto della chiamata del metodo della classe originale, è sufficiente che il metodo _ereditato_ soddisfi la specifica del metodo _originale_.
Questo **NON** è verificabile staticamente dal compilatore.
In termini non formali un metodo _ereditato_ soddisfa la specifica del metodo _originale_ se ha una precondizione più _debole_ (richiede meno) ed una postcondizione più _forte_ (promette di più). Formalizziamolo.

#### Condizioni _forti_ e _deboli_

Una condizione è _più forte_ di un altra se è _vera "in meno casi"_.
Questo concetto si formalizza in logica attraverso l'implicazione: una condizione `a` è **_più forte_**  di una condizione `b` se è sempre vera la condizione `a ==> b`.
Questo introduce un ordinamento (non totale) delle formule logiche dalla _più forte_ alla _più debole_. In particolare `false` è la condizione _più forte_ in assoluto e `true` la _più debole_ in assoluto.

Vediamo l'**effetto degli operatori logici** sulla `forza` delle condizioni:
- `||` _indebolisce_: `a ==> a || b` (cioè `a || b` è _più debole_ di `a`)
- `&&` _rafforza_: `a && b ==> a` (cioè `a && b` è _più forte_ di `a`)
- `==>` _indebolice_: `a ==> (b ==> a)`, si deduce ricordando che `b ==> a` equivale ad `!b || a`
- se _rafforziamo_ la premessa _indeboliamo_ l'implicazione:
supponiamo che `c` sia _più forte_ di `a`, allora è sempre vero `c ==> a`.
Allora, se `a ==> b` è vero, per transitività `c ==> b` è vero, cioè abbiamo dimostrato che `(a ==> b) ==> (c ==> b)` e cioè che `a ==> b` è _più forte_ di `c ==> b`.
