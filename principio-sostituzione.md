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
- _method rule_: le chiamate ad un metodo della <br>sottoclasse si devono "comportare" come le chiamate <br>al metodo corrispondente della superclasse
- _property rule_: una sottoclasse deve preservare tutte le proprietà astratte (vedi capitolo sul JML) degli oggetti della superclasse

La _signature rule_ garantisce che la sintassi con cui operiamo sulla sottoclasse sia compatibile con la sintassi della superclasse.
La _method rule_ garantisce che il contratto (inteso come la specifica) di ciascun metodo _ereditato_ sia compatibile con il contratto del metodo _originale_. In particolare un'estensione si dice **pura** se non cambia la specifica (aggiunge solo dei metodi).
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

### _Method rule_

Perché la chiamata di un metodo di una sottoclasse abbia lo stesso effetto della chiamata del metodo della classe originale, è sufficiente che il metodo _ereditato_ soddisfi la specifica del metodo _originale_.
Questo **NON** è verificabile staticamente dal compilatore.
In termini non formali un metodo _ereditato_ soddisfa la specifica del metodo _originale_ se ha una precondizione più _debole_ (richiede meno) ed una postcondizione più _forte_ (promette di più). Formalizziamolo.

#### Condizioni _forti_ e _deboli_

Una condizione è _più forte_ di un'altra se è _vera "in meno casi"_.
Questo concetto si formalizza in logica attraverso l'implicazione: una condizione `a` è **_più forte_**  di una condizione `b` se è sempre vera la condizione `a ==> b`.
Questo introduce un ordinamento (non totale) delle formule logiche dalla _più forte_ alla _più debole_. In particolare `false` è la condizione _più forte_ in assoluto e `true` la _più debole_ in assoluto.

Vediamo l'**effetto degli operatori logici** sulla `forza` delle condizioni:
- `||` _indebolisce_: `a ==> a || b` (cioè `a || b` è _più debole_ di `a`)
- `&&` _rafforza_: `a && b ==> a` (cioè `a && b` è _più forte_ di `a`)
- `==>` _indebolisce_: `a ==> (b ==> a)`, si deduce ricordando che `b ==> a` equivale ad `!b || a`
- se _rafforziamo_ la premessa _indeboliamo_ l'implicazione:
supponiamo che `c` sia _più forte_ di `a`, allora è sempre vero `c ==> a`.
Allora, se `a ==> b` è vero, per transitività `c ==> b` è vero, cioè abbiamo dimostrato che `(a ==> b) ==> (c ==> b)` e cioè che `a ==> b` è _più forte_ di `c ==> b`.

#### Precondizione _più debole_

Se la precondizione del metodo _ereditato_ è più debole di quella del metodo _originale_ allora se è vera la precondizione del metodo _originale_ è anche vera quella del metodo _ereditato_ e cioè possiamo richiamare il metodo _ereditato_ in tutti i casi in cui potevano richiamare quello _originale_; proprio come ci aspetteremmo!
Quindi condizione **necessaria** perchè valga la _method rule_ è la **_precondition rule_**: detta `pre_sub` la precondizione del metodo _ereditato_ e `pre_super` la precondizione di quello _originale_, `pre_sub` è _più debole_ di `pre_super` e cioè `pre_super ==> pre_sub` è sempre vera.

Se `pre_sub` non fosse _più debole_ di `pre_super` esisterebbe un caso in cui _pre_sub_ è falsa e _pre_super_ è vera. L'utente richiamando il metodo in quel caso (che soddisfa la precondizione del metodo _originale_ e quindi risulta un caso valido di input) otterrebbe un risultato inaspettato (dato che tale caso viola la precondizione del metodo _ereditato_ che è quello che viene effettivamente invocato).

#### Postcondizione _più forte_

Alla fine dell'esecuzione del metodo _ereditato_ ci aspettiamo che la postcondizione del metodo _originale_, detta `post_super` sia soddisfatta. L'utente, nella sua implementazione, infatti fa riferimento solo alla postcondizione del metodo _originale_ e non deve preoccuparsi se in realtà ad essere invocato è il metodo _ereditato_. Quindi, detta `post_sub` la postcondizione del metodo _ereditato_, una condizione **sufficiente** (assumendo che la _precondition rule_ sia stata rispettata) perchè valga la _method rule_ è che `post_sub` sia più forte di `post_super`, ovvero `post_sub ==> post_super`. In questo modo, dato che il metodo _ereditato_ deve soddisfare la sua postcondizione, soddisferà automaticamente anche le postcondizione del metodo _originale_.

---

In realtà questa condizione è più stringente del necessario. L'utente invocherà il metodo solo nei casi che soddisfano la precondizone del metodo **_originale_** ed abbiamo visto che in generale la precondizione del metodo _ereditato_ può "ammettere più casi". Quindi ci basta che valga la **_full postcondition rule_** cioè che `post_sub` implichi che `post_super` sia vera se `pre_super` era vera al momento della chiamata del metodo, che in formule diventa: `post_sub ==> (\old(pre_super) ==> post_super)`.
Sulle slide la _full postcondition rule_ è espressa come `(\old(pre_super) && post_sub) ==> post_super` (in realtà senza `\old` ma è più corretto aggiungerlo); le due formule sono equivalenti, infatti `post_sub ==> (\old(pre_super) ==> post_super) = !post_sub || (!\old(pre_super) || post_super) = (!\old(pre_super) || !post_sub) || post_super = !(!\old(pre_super) || !post_sub) ==> post_super = (\old(pre_super) && post_sub) ==> post_super`.

#### Specificare metodi che ne estendono altri in JML

Per specificare un metodo che ne estende un altro in JML si utilizza la keyword `also` che si inserisce nella specifica in questo modo:
```java
//@ also
//@ requires pre_ext;
//@ ensures post_ext;
```

Notiamo che in `requires` ed `ensures` compaiono `pre_ext` e `post_ext` invece di `pre_sub` e `post_sub`. Questo perchè la semantica della specifica con `also` si traduce in:
```java
//@ requires pre_super || pre_ext;
//@ ensures (\old(pre_super) ==> post_super)
//@   && (\old(pre_ext) ==> post_ext);
```

Quindi `pre_sub = pre_super || pre_ext` e `post_sub = (\old(pre_super) ==> post_super) && (\old(pre_ext) ==> post_ext)`.

Notiamo che `pre_sub` è più debole di `pre_super` e che, dato che `&&` rafforza, vale `post_sub ==> (\old(pre_super) ==> post_super)`. Quindi i metodi ottenuti per estensione, se specificati attraverso JML, **soddisfano sempre la _method rule_** dato che valgono la _**precondition rule**_ e la _**full postcondition rule**_.

Osserviamo che specificando i metodi con `also`:
- **Non possiamo _rafforzare_ la precondizione**: supponiamo `pre_ext` _più forte_ di `pre_super`, allora `pre_ext ==> pre_super` è sempre vera, allora `!pre_ext || pre_super = true`, allora `pre_ext && !pre_super = false`, allora `pre_sub = pre_super || pre_ext = pre_super || pre_ext && true = pre_super || pre_ext && (pre_super || !pre_super) = pre_super || pre_ext && pre_super || pre_ext && !pre_super = pre_super && true || pre_super && pre_ext || false = pre_super && (true || pre_ext) = pre_super && true = pre_super`
- **Non possiamo _indebolire_ la postcondizione**: supponiamo `post_ext` _più debole_ di `post_super`, allora `post_super ==> post_ext` è sempre vera, allora, nell'ipotesi che `\old(pre_super)` sia verificata, `post_sub = (true ==> post_super) && (\old(pre_ext) ==> post_ext) = post_super && (\old(pre_ext) ==> post_ext) = post_super` (se `post_super` vale `false` allora `post_sub = post_super && ...` vale `false`, se `post_super` vale `true`, allora `post_ext` vale `true`, allora anche `\old(pre_ext) ==> post_ext` vale `true`, allora `post_sub` vale `true`).
- **Se volessimo semplicemente _rafforzare_ la postcondizione è sufficiente che `pre_ext = pre_super` e che `post_ext` sia _più forte_  di `post_super`**: `pre_sub = pre_super || pre_ext = pre_super || pre_super = pre_super` e, supponendo che `\old(pre_super) = \old(pre_ext)` sia verificata, `post_sub = (\old(pre_super) ==> post_super) && (\old(pre_ext) ==> post_ext) = (true ==> post_super) && (true ==> post_ext) = post_super && post_ext = post_ext` (se `post_ext` vale `false` allora `post_sub = ... && post_ext` vale `false`, se `post_ext` vale `true` allora anche `post_super` vale `true`, allora `post_sub` vale `true`)


#### Eliminare le eccezioni

Abbiamo già spiegato che è possibile rimuovere alcune delle eccezioni quando si fa un override di un metodo, senza violare la _signature rule_.
Dobbiamo però fare molta attenzione che la _method rule_ sia ancora soddisfatta.
Consideriamo la seguente classe:
```java
public class InsiemeDiInteriEccezDuplicati {
  ...
  //@ ensures !\old(appartiene(x)) &&
  //@   appartiene(x) && ...;
  //@ signals (EccezioneDuplicato e)
  //@   \old(appartiene(x));
  public void inserisci(int x)
    throws EccezioneDuplicato;
  ...
}
```
che restituisce un'eccezione quando si prova ad inserire un elemento già presente nell'insieme.
Per ipotesi
```java
public class InsiemeDiInteri
  extends InsiemeDiInteriEccezDuplicati {
  ...
  //@ ensures appartiene(x) &&
  //@ cardinalita() == \old(cardinalita() +
  //@ (appartiene(x) ? 0 : 1)) &&
  //@ (\forall int y; \old(appartiene(y));
  //@ appartiene(y));
  public void inserisci(int x);
  ...
}
```
supponiamo che `InsiemeDiInteri` sia una **sottoclasse** di `InsiemeDiInteriEccezDuplicati` e che ridefinisca il metodo `inserisci` secondo la specifica che abbiamo introdotto originariamente (nel capitolo _JML_).
Secondo ciò che abbiamo detto `InsiemeDiInteri` soddisfa la _signature rule_.
Un utente di `InsiemeDiInteriEccezDuplicati` però, si aspetta di ricevere un'eccezione se inserisce un elemento due volte di seguito nell'insieme, ma questo **NON** avviene se il tipo dinamico dell'insieme è `InsiemeDiInteri`.

---

Quindi, in questo esempio, `InsiemeDiInteri` **viola** la _method rule_ e **NON** rispetta il _principio di sostituzione_.

### _Property rule_

Una classe gode di due macrocategorie di proprietà astratte: le proprietà _invarianti_ e le proprietà _evolutive_ (vedi capitolo sul _JML_).
Le prime possono essere esplicitate in JML attraverso il costrutto `public invariant`, ma questo non avviene sempre; al contrario le seconde sono deducibili solo considerando le specifiche di tutti i metodi della classe, nel loro complesso.
Perchè una **sottoclasse** soddisfi la _property rule_, deve conservare le proprietà astratte della classe che estende, **per tutti gli stati astratti osservabili tramite gli osservatori della classe _originale_**. Non è infatti necessario che le proprietà astratte della classe _originale_ valgano anche per la "porzione" di stato astratto della classe _derivata_ che è osservabile tramite dei metodi presenti solo in quest'ultima.

Ad esempio se una classe _immutabile_ `A` viene estesa da una classe `B` definita come segue:
```java
public class B extends A {
  private int b;

  public void setB(int b) { this.b = b; }

  public int getB() { return b; }
}
```
Nonostante `B` sia chiaramente _mutabile_, la "porzione" del suo stato astratto che muta (l'attributo `b`) non è osservabile con gli _observer_ di `A`: quindi `B` soddisfa la _property rule_ (non viola la proprietà evolutiva di _immutabilità_ rispetto allo stato osservabile dagli utenti di `A`).

A differenza della _signature rule_ e della _method rule_, nulla garantisce che la _property rule_ sia stata rispettata, quindi è necessario valutarlo volta per volta in base alle specifiche di tutti i metodi della classe.

<br>

#### Esempio di violazione di una proprietà invariante

Consideriamo la classe `InsiemeDiInteriPieno`, ovvero un `InsiemeDiInteri` che non è mai vuoto:
```java
public class InsiemeDiInteriPieno {
  // OVERVIEW: Insieme di interi illimitato
  //   e mutabile con almeno un elemento
  
  //@ public invariant cardinalita() >= 1;

  //@ ensures (* restituisce un
  //@   InsiemeDiInteriPieno che rappresenta
  //@   l'insieme { i } *);
  public InsiemeDiInteriPieno(int i);

  //@ ensures (\old(cardinalita() >= 2) ==>
  //@   !appartiene(x)) &&
  //@   ((\old(cardinalita() == 1)) ==>
  //@   (* l'insieme rimane invariato *));
  public void rimuoviSeNonVuoto(int x);
}
```

Supponiamo che `InsiemeDiInteri` sia una **sottoclasse** di `InsiemeDiInteriPieno` che aggiunge il metodo `rimuovi` così come lo avevamo definito originariamente:
```java
public class InsiemeDiInteri
  extends InsiemeDiInteriPieno {
  
  //@ ensures !appartiene(x) &&
  //@ cardinalita() == \old(cardinalita() -
  //@   (appartiene(x) ? 1 : 0)) &&
  //@ (\forall int y; appartiene(y);
  //@   \old(appartiene(y)));
  public void rimuovi(int x);
}
```

Dato che `InsiemeDiInteri` non ridefinisce alcun metodo di `InsiemeDiInteriPieno`, la _signature rule_ e la _method rule_ risultano soddisfatte.
Grazie però al nuovo metodo `rimuovi` possiamo violare l'invariante pubblico di `InsiemeDiInteriPieno` svuotando l'insieme.
Quindi, in questo esempio, `InsiemeDiInteri` **viola** la _property rule_ e di conseguenza **NON** rispetta il _principio di sostituzione_.

#### Esempio di violazione di una proprietà evolutiva

Consideriamo la classe `InsiemeDiInteriSenzaRimuovi` che è uguale ad `InsiemeDiInteri` ma non ha il metodo `rimuovi`.
`InsiemeDiInteriSenzaRimuovi` gode della seguente proprietà _evolutiva_: _"il valore restituito da `cardinalita` nello stato prossimo è maggiore o uguale a quello restituito nello stato corrente"_ (l'insieme non si "restringe").
Supponiamo che la classe `InsiemeDiInteri` estenda la classe `InsiemeDiInteriSenzaRimuovi` aggiungendo, come nell'esempio precedente, solo il metodo `rimuovi` definito come al solito.
Come nell'esempio precedente la _signature rule_ e la _method rule_ non possono essere violate, dato che `InsiemeDiInteri` non ridefinisce alcun metodo.
Chiaramente ad essere violata è la proprietà evolutiva di `InsiemeDiInteriSenzaRimuovi` e di conseguenza la _property rule_.
