# JML

**JML** (Java Modeling Language) è un linguaggio di specifica formale.

## Sintassi

Lo schema generale di una specifica in JML è il seguente:
```java
// OVERVIEW: descrizione della specifica
//@ assignable <parametri che possono essere 
//@    modificati dal metodo>;
//@ requires <precondizione>
//@ ...;
//@ ensures <postcondizione>
//@ ...;
//@ signals (<tipo eccezione 1> e)
//@ <postcondizione nel caso di eccezione 1>
//@ ...;
//@ signals (<tipo eccezione 2> e)
//@ <postcondizione nel caso di eccezione 2>
//@ ...;
```
Ogni riga della specifica (dopo l'`OVERVIEW`) inizia con `//@ `.
Alla fine di ciascun "blocco" (`assignable`, `requires`, ...) è necessario aggiungere `;`.
Omettere il blocco `requires` equivale a scrivere `//@ requires true;`.
Omettere il blocco `ensures` equivale a scrivere `//@ ensures true;`.
Nella condizione del blocco `signals` possiamo fare riferimento all'oggetto eccezione `e` (il nome è arbitrario).

### Condizioni

Le condizioni in JML (precondizioni e postcondizioni) sono espressioni booleane di Java (con alcuni operatori e quantificatori aggiuntivi) che non alterano lo stato degli oggetti che descrivono: non si possono usare assegnamenti (`=`), incrementare le variabili intere (`++`), etc. Gli unici metodi che si possono invocare sono quelli che non modificano lo stato degli oggetti a cui appartengono o dei parametri che gli vengono passati (si dicono **metodi puri**).

#### Operatori booleani aggiuntivi

Siano `a` e `b` due condizioni JML, allora le seguenti sono valide condizioni JML:

- `a ==> b`: `a` implica `b`
- `a <== b`: `b` implica `a`
- `a <==> b`: `a` se e solo se `b`
- `a <=!=> b`: `!(a <==> b)`

#### `\old`

L'operatore `\old(<espressione>)` prende in input una espressione che può essere una condizione JML oppure una espressione Java che non ha "effetti collaterali" (non si può utilizzare `++`, `=`, metodi **non** puri, etc.) e restituisce il risultato che si ottiene valutando tale espressione nel momento della chiamata del metodo che stiamo specificando.
Notare che, valutando una espressione Java (tra quelle ammissibili), `\old` in generale non restituisce valori booleani.
Non ha senso utilizzare `\old` nel blocco `requires` dato che lì stiamo specificando ciò che deve essere vero **prima** che il metodo venga eseguito.

#### Quantificatori

Sia `T` un generico tipo di Java ed `a(t)`, `b(t)` due condizioni JML definite su un oggetto `t` di tipo `T` (ad esempio se `T = int`, `a(t) = t > 1729`), allora le seguenti sono valide condizioni JML:

- `(\forall T t; a(t); b(t))`: per ogni oggetto del tipo `T` se `a(t)` allora `b(t)`
- `(\exists T t; a(t); b(t))`: esiste un oggetto del tipo `T` tale che `a(t)` e `b(t)`
- `(\num_of T t; a(t); b(t))`: restituisce il numero di oggetti `t` tale che `a(t)` e `b(t)`

Nel caso `T` non sia un tipo primitivo assumiamo `t != null`.

#### Operatori di aggragazione

Sia `T` un generico tipo di Java ed `N` uno dei tipi numerici primitivi di Java (`int`, `float`, ...).
Sia `a(t)` una condizione JML definita sull'oggetto `t` di tipo `T`.
Sia `b : T -> N` una funzione (in senso matematico) implementata attraverso Java. Ad esempio:
`T = String`, `N = int`, `a(t) = !t.isEmpty() && t.charAt(0) == 'e'`, `b(t) = t.length()`.
Allora possiamo applicare i seguenti operatori di aggragazione:

- `(\sum T t; a(t); b(t))`: restituisce la somma `b(t_1) + b(t_2) + ...` per tutti i `t_i` tali che `a(t_i)`
- `(\product T t; a(t); b(t))`: restituisce il prodotto `b(t_1)*b(t_2)*...` per tutti i `t_i` tali che `a(t_i)`
- `(\max T t; a(t); b(t))`: restituisce il massimo tra `b(t_1), b(t_2), ...` per tutti i `t_i` tali che `a(t_i)`
- `(\min T t; a(t); b(t))`: restituisce il minimo tra `b(t_1), b(t_2), ...` per tutti i `t_i` tali che `a(t_i)`

### `\result`

Se stiamo scrivendo la specifica di un metodo NON `void`, possiamo fare riferimento al valore restituito con la keyword `\result`.
Ha senso utilizzare `\result` solo nell'`ensures` (in `requires` il metodo non è ancora stato eseguito, `signals` specifica la postcondizione qualora venga restituita un'eccezione).

### `assignable`

Il blocco `assignable` nella specifica permette di esplicitare i parametri (di tipo riferimento) che vengono modificati dal metodo.
Omettere `assignable` significa che tutti i parametri possono essere modificati.

Se un metodo non modifica nessuno dei parametri possiamo usare la keyword `\nothing`:
`//@ assignable \nothing;`.

Consideriamo il seguente metodo:
```java
public static void metodo(S s, T t, U u) {
    ...
}
```
Per specificare che `s` e `t` vengono modificati, ma non `u`, possiamo aggiungere nella specifica:
`//@ assignable s, t;`

---

Supponiamo di voler specificare che un array `a[]` venga modificato da un metodo di cui stiamo scrivendo la specifica:

- `//@ assignable a[*];`: ogni elemento di `a` può essere modificato
- `//@ assignable a[5];`: solo l'elemento `a[5]` può essere modificato
- `//@ assignable a[1..8];`: gli elementi `a[1]`, `a[2]`, ..., `a[8]` possono essere modificati

### Commenti

A volte è utile inserire all'interno delle condizioni JML delle specifiche informali.
Per farlo si utilizzano i commenti, esprimibili attraverso la seguente sintassi: `(* <commento> *)`.
Ciascun commento al momento della valutazione della condizione è da intendersi con valore `true`.

## Semantica

### Precondizione

La **precondizione** è la condizione sulla base della quale è definita la specifica: se la precondizione non dovesse essere rispettata allora non è detto che il metodo si comporti secondo la specifica (in generale non lo farà, qualsiasi comportamento è ammesso).
In JML è possibile esprimere una precondizione del metodo che stiamo specificando attraverso il blocco `requires`.
Nel caso in cui la precondizione sia `true` il metodo "non ha una precondizione": la sua specifica è valida a prescindere dei parametri passati.
Un metodo con precondizione `true` si dice **totale**, altrimenti si dice **parziale**.

### Postcondizione

La **postcondizione** esplicita una serie di "effetti" garantiti al termine dell'esecuzione del metodo che stiamo specificando, assumendo che la precondizione fosse verificata.
In JML è possibile definire separatamente la postcondizione che vale nel caso in cui il metodo esegua regolarmente dalle postcondizioni che valgono nel caso in cui durante l'esecuzione del metodo si verifichino delle eccezioni.
La prima si esplicita attraverso il blocco `ensures`.
La seconda attraverso `signals (<tipo eccezione> e)`.
Nel caso in cui la postcondizione sia `true` il metodo non garantisce nessun "effetto" al termine della sua esecuzione, quindi può "fare ciò che vuole": non c'è motivo di omettere la postcondizione.

<!-- TODO:
 - assertions (di secondaria importanza)  -->

 ## Astrazione procedurale

Si dice **astrazione procedurale** la specifica di un'operazione (anche complessa) definita su un dominio di dati generici (parametri).
In Java coincide con la specifica (ad esempio attraverso la notazione JML) di un metodo statico.
Infatti un metodo statico rappresenta proprio un'operazione "priva di stato": il suo comportamento non dipende dai valori di attributi non statici, ma è determinato unicamente dai parametri.

## ADT: Abstract Data Type

Si dice **abstract data type** (o **ADT**) un tipo di dato per cui tutti gli stati ammissibili e le operazioni che vi si possono effettuare (includendo il modo in cui quest'ultime permettono di passare da uno stato all'altro) sono descritti attraverso una specifica.
La specifica di un ADT si compone di una sintassi e di una semantica.
La sintassi coincide con l'interfaccia del tipo di dato in questione (l'insieme di metodi pubblici che espone). Per definire la semantica in maniera esaustiva occorre utilizzare un linguaggio di specifica formale come JML.
A differenza dell'astrazione procedurale, nello specificare un ADT con JML, dobbiamo trattare anche le transizioni di stato dell'oggetto dovute alle varie operazioni (cioè dire ciò che cambia, come cambia e cosa invece rimane invariato tra i valori che rappresentano lo stato dell'oggetto a seguito dell'esecuzione di un certo metodo).

### Metodi puri

Un metodo **di un ADT** si dice **puro** se:
 - vale `//@ assignable \nothing;`
 - gli unici metodi che invoca sono anche essi puri
 - non modifica nessun attributo (pubblico o privato) dell'ADT

I metodi puri si indicano in JML con la keyword `/* @ pure @ */`.
Ad esempio, supponiamo che il metodo `dimensione` restituisca la cardinalità di un ADT che rappresenta una collezione di oggetti.
`dimensione` è chiaramente un metodo puro, in quanto non modifica lo stato della collezione, per esplicitarlo in JML possiamo usare la sintassi: `public int /* @ pure @ */ dimensione();`.

Anche un costruttore può essere **puro** se si limita ad inizializzare gli attributi dell'oggetto senza apportare altre modifiche.

I metodi puri si dicono anche **observers** in quanto permettono di "osservare" lo stato di un ADT in un determinato momento.

### Classi pure

Una classe i cui metodi **pubblici** (e costruttori) sono tutti **puri** si dice **pura** e si indica con la sintassi:
`public /* @ pure @ */ class NomeClasse`.
Una classe **pura** è una classe **immutabile**.

**Attenzione**: quando specifichiamo che una classe è **pure** **NON** è necessario che nella specifica si espliciti che il suo stato non cambia (cioè che tutti gli observer restituiscono gli stessi risultati prima e dopo l'esecuzione del metodo).
Questo risulterà utile in seguito per alleggerire la specifica in JML dei metodi.

### Specifica di un'operazione di un ADT in JML

Valgono le regole sintattiche e semantiche già introdotte per JML.
La struttura della specifica rimane quella usuale.

**Attenzione**: quando specifichiamo un'operazione di un ADT in JML, nella specifica possono comparire solo gli altri metodi (e attributi) **pubblici** e **puri** (dell'ADT), i parametri formali dell'operazione (su cui possiamo invocare i rispettivi metodi **pubblici** e **puri**) e `\result` per fare riferimento al risultato restituito.

---

### Esempio

Vediamo un esempio di ADT.

Vogliamo descrivere attraverso la specifica un _insieme (mutabile) di interi_ su cui sono definite le seguenti operazioni:
- _costruzione_: crea ed inizializza l'insieme come un insieme vuoto
- _inserisci(x)_: aggiunge l'elemento x all'insieme
- _rimuovi(x)_: rimuove l'elemento x dall'insieme
- _appartiene(x)_: restituisce _vero_ se x appartiene all'insieme, _falso_ altrimenti
- _cardinalità_: resituisce la cardinalità dell'insieme
- _scegli_: restituisce uno tra gli elementi dell'insieme

Alcuni valori ammissibili per l'insieme sono: _{1, 10, 35}_, _{7}_, ...

```java
public class InsiemeDiInteri {
  // OVERVIEW: Insieme di interi illimitato
  //  e mutabile
  
  // Observers:

  //@ ensures (* \result equivale a
  //@ "x appartiene all'insieme" *);
  public /* @ pure @ */
    boolean appartiene(int x);

  //@ ensures \result ==
  //@   (\num_of int x; ; appartiene(x))
  public /* @ pure @ */ int cardinalita();

  //@ ensures appartiene(\result) &&
  //@ cardinalita() > 0;
  //@ signals (EccezioneInsiemeVuoto e)
  //@ cardinalita() == 0;
  public /* @ pure @ */ int scegli()
    throws EccezioneInsiemeVuoto;

  // Creator:

  //@ ensures cardinalita() == 0;
  public InsiemeDiInteri();

  // Modifiers:

  //@ ensures appartiene(x) &&
  //@ cardinalita() == \old(cardinalita() +
  //@   (appartiene(x) ? 0 : 1)) &&
  //@ (\forall int y; \old(appartiene(y));
  //@   appartiene(y));
  public void inserisci(int x);

  //@ ensures !appartiene(x) &&
  //@ cardinalita() == \old(cardinalita() -
  //@   (appartiene(x) ? 1 : 0)) &&
  //@ (\forall int y; appartiene(y);
  //@   \old(appartiene(y)));
  public void rimuovi(int x);
}
```

Osserviamo che **NON** tutti i metodi pubblici dell'oggetto possono essere specificati formalmente (ovvero senza dover ricorrere ai commenti) in JML. Questo in particolare è vero per alcuni degli **observer**, nel caso d'esempio: `appartiene`.
Per poter specificare formalmente questi metodi sarà necessario dichiarare un **rappresentante**, cioè un oggetto che realizza lo stato concreto dell'ADT, (spiegato in seguito) e fare riferimento all'implementazione.

Un ADT deve consentire di utilizzare gli oggetti che descrive, senza conoscerne l'implementazione. Vediamo come implementare, conoscendo solo la specifica, un metodo che crea un `InsiemeDiInteri` a partire da un array di interi:
```java
public static InsiemeDiInteri daArray(int[] a)
  throws NullPointerException {
  
  if (a == null) {
    throw new NullPointerException();
  }

  InsiemeDiInteri s = new InsiemeDiInteri();
  // Dalla specifica s è vuoto.

  for (int x : a) {
    s.inserisci(x);
  }
  // Dalla specifica s contiene tutti
  // e soli gli interi (x) in a

  return s;
}
```

### Categorie di operazioni

Possiamo classificare le operazioni (i metodi pubblici) definite su un ADT nelle seguenti categorie:
- **_Creators_**: creano un nuovo oggetto del tipo definito dall'ADT prendendo in input parametri che **NON** sono altri oggetti del tipo definito dall'ADT
- **_Producers_**: creano un nuovo oggetto del tipo definito dall'ADT prendendo in input un oggetto del tipo definito dall'ADT
- **_Mutators_**: modificano lo stato dell'oggetto
- **_Observers_**: restituiscono un risultato di un tipo diverso da quello definito dall'ADT; solitamente non modificano l'oggetto e quindi sono dichiarati come puri

Un tipo _mutabile_ "adeguato" dovrebbe disporre di _creators_, _observers_ e _mutators_.

Un tipo _immutabile_ "adeguato" dovrebbe disporre di _crators_, _observers_ e _producers_.

### Proprietà astratte (evolutive e invarianti)

Si dicono proprietà **astratte** di un ADT tutte le proprietà di cui esso gode, che sono deducibili dalla specifica dei suoi metodi pubblici.
Si distinguono in:
- Proprietà **evolutive**: specificano la relazione tra uno stato osservabile ed il successivo (ovvero specificano come l'oggetto evolve). Un esempio di proprietà evolutiva è l'immutabilità, che può essere espressa attraverso il concetto di stato corrente e successivo come segue: "Per ogni stato corrente dell'oggetto, per ogni operazione, detto stato successivo lo stato in cui si trova l'oggetto dopo aver eseguito l'operazione, lo stato corrente coincide con lo stato successivo"
- Properità **invarianti**: si tratta di proprietà che sono valide per qualunque stato ammissibile dell'oggetto. Nell'esempio `InsiemeDiInteri`, una proprietà invariante è: `cardinalita() >= 0`.

Le proprietà **evolutive** **NON** sono **rappresentabili direttamente in JML**: non esiste una sintassi per dichiararle esplicitamente, ma seguono dalle specifiche dei singoli metodi.

---

Al contrario, per **rappresentare in JML** una proprietà **invariante**, anche detta **invariante pubblico**, si usa la seguente sintassi:
```java
public class ClasseADT {
  //@ public invariant <condizione>;

  ...
}
```

Le proprietà astratte permettono agli utenti dell'ADT di fare assunzioni che ne semplificano l'utilizzo.

#### Dimostrare la validità di un invariante pubblico

Dichiarare un invariante pubblico non è sufficiente per garantirne la validità.
Dobbiamo assicurarci, attraverso la specifica, che l'invariante sia valido per tutti gli stati "iniziali" delle istanze dell'ADT: ovvero gli oggetti ottenuti invocando i creators. Successivamente è necessario verificare che, a partire da un generico stato ammissibile dell'oggetto, applicando una qualsiasi delle operazioni definite e assumendo vere le rispettive precondizioni, la proprietà sia ancora valida.
In particolare uno stato si considera "ammissibile" se è raggiungibile applicando un nunmero finito di volte le operazioni dell'ADT ad uno degli stati iniziali.
Non è necessario dimostrare che gli observer soddisfino l'invariante, dato che non modificano lo stato dell'oggetto.

### Rappresentante

Per **implementare** un ADT è necessario dichiarare un **rappresentante** (o **`rep`**), ovvero una _struttura dati_ in grado di rappresentare, attraverso i valori che assume, lo stato concreto dell'ADT.
In Java questo si traduce in un insieme di attributi **privati**.
Ricordiamo che l'utente deve poter utilizzare l'ADT conoscendo esclusivamente la sua specifica, quindi non è necessario (anzi vedremo essere una pratica scorretta) esporre il rappresentante dello stato concreto (magari dichiarandolo pubblico).

Nell'esempio `InsiemeDiInteri` un rappresentante molto semplice, ma efficace, è un `ArrayList<Integer>` che contiene gli elementi dell'insieme.
Vediamo una possibile implementazione:
```java
public class InsiemeDiInteri {
  private ArrayList<Integer> rep;

  public boolean appartiene(int x) {
    return trova(x) != -1;
  }

  public int cardinalita() {
    return rep.size();
  }

  public int scegli() throws
      EccezioneInsiemeVuoto {
    if (rep.size() == 0) {
      throw new EccezioneInsiemeVuoto();
    }
    return rep.get(0);
  }

  public InsiemeDiInteri() {
    rep = new ArrayList<>();
  }

  public void inserisci(int x) {
    if (appartiene(x)) { return; }
    rep.add(x);
  }

  public void rimuovi(int x) {
    int iX = trova(x);
    if (iX == -1) { return; }
    rep.remove(iX);
  }

  // trova è un metodo di ausilio che cerca
  // x in rep e, se lo trova
  // restituisce l'indice corrispondente,
  // altrimenti -1
  private /* @ helper @ */ int trova(int x) {
    for (int i = 0; i < rep.size(); i++) {
      if (rep.get(i) == x) { return i; }
    }
    return -1;
  }
}
```

### Funzione di astrazione

Si dice **funzione di astrazione** (o **AF**) una funzione (in senso matematico) che associa ad ogni stato concreto ammissibile, rappresentato dal `rep`, lo stato astratto (dell'ADT) che vi corrisponde.
Nell'esempio `InsiemeDiInteri` lo stato concreto è un `ArrayList<Integer>` come ad esempio `[4, 1, 2, 3]`. L'AF associa `[4, 1, 2, 3]` all'insieme `{1, 2, 3, 4}` che è proprio lo stato astratto dell'ADT corrispondente a tale `ArrayList`.
Le funzioni di astrazione possono risultare più o meno complicate e **dipendono** dall'implementazione scelta.
Solitamente sono **NON** iniettive: più stati concreti corrispondono allo stesso stato astratto. Nell'esempio `[4, 1, 2, 3]` e `[1, 2, 3, 4]` corrispondono entrambi all'insieme `{1, 2, 3, 4}`.

#### Come dichiarare l'AF in JML

In JML è possibile **dichiarare** (**NON** implementare) la funzione di astrazione attraverso la seguente sintassi:
```java
public class ClasseADT {
  ...
  // AF:
  //@ private invariant
  //@ <condizione>;
  ...
}
```
L'AF viene dichiarata all'interno del blocco JML **private invariant**, che ci consente di accedere, oltre che agli attributi e metodi pubblici della classe, **anche a quelli privati**.
Nella condizione JML siamo interessati ad esplicitare la **relazione** (logica) che sussiste tra lo stato concreto e lo stato astratto corrispondente dell'ADT. Cioè non vogliamo spiegare cosa la funzione fa (la sua implementazione) ma solo le proprietà che devono valere perchè uno stato concreto ed uno astratto siano corrispondenti.
Nell'esempio `InsiemeDiInteri` con un'`ArrayList` come `rep`, a prescindere da come l'AF venga realizzata, vale che _"un elemento `x` appartiene all'insieme s (stato astratto) sse esiste un indice i compreso tra 0 e `rep.size()` tale che `rep.get(i) == x` (stato concreto)"_.
Lo stato concreto è rappresentato dal `rep`, a cui possiamo accedere dato che è costituito da un insieme di attributi privati (ricordiamo che siamo nel private invariant). 
Lo stato astratto invece non è realmente memorizzato da nessuna parte, è possibile accedervi solo attraverso gli _observer_.

---

Quindi nella condizione JML compariranno gli attributi **privati** che costituiscono il `rep` ed gli _observer_ che permettono di osservare lo stato astratto dell'ADT, legati tra loro attraverso delle formule logiche che risultano vere solo quando i valori assunti dagli attributi **privati** corrispondono con lo stato astratto osservato.
Dichiariamo l'AF nell'esempio `InsiemeDiInteri`:
```java
public class InsiemeDiInteri {
  ...
  // AF:
  //@ private invariant
  //@ (\forall int x; ;
  //@   appartiene(x) <==>
  //@   (\exists int i; 0 <= i &&
  //@     i < rep.size(); rep.get(i) == x));
  ...
}
```

Notiamo che siamo finalmente riusciti a specificare formalmente il metodo `appartiene` che, prima dell'introduzione de `rep`, era semplicemente descritto attraverso un commento in JML.

#### Come implementare l'AF

Per **implementare** l'AF solitamente si ricorre ad una rappresentazione testuale (tramite una stringa) degli stati astratti, quindi si ridefinisce `toString`.
Nell'esempio `InsiemeDiInteri` una possibile implementazione dell'AF (attraverso i paradigmi della programmazione funzionale) è quella che segue:
```java
public class InsiemeDiInteri {
  ...
  @Override
  public String toString() {
    return rep.stream().sorted()
      .map(x -> x.toString())
      .collect(Collectors
        .joining(", ", "{", "}"));
  }
}
```
Osserviamo che l'ordinamento della lista di interi prima della stampa fa in modo che gli stati astratti corrispondenti a `[1, 2, 3, 4]` e `[4, 3, 2, 1]`, **che sono uguali**, siano rappresentati da un'unica stringa `"{1, 2, 3, 4}"`.

### Invariante di rappresentazione

**NON** tutti gli stati concreti assunti dal `rep` sono rappresentanti ammissibili di uno stato astratto.
Nell'esempio `InsiemeDiInteri` risulta evidente che i seguenti valori per il `rep` non costituiscno degli stati ammissibili:
- `null`
- `[1, null, 3]`

Ci sono però altre assunzioni (implicite) che facciamo nell'implementazione di `InsiemeDiInteri` che rendono inammissibili anche altri stati concreti che potrebbero sembrare validi.
Ad esempio, quando rimuoviamo un elemento dall'insieme, rimuoviamo dal `rep` al più un elemento all'indice `iX` (in particolare rimuoviamo l'elemento che vale `x` con indice minimo, se esiste). Quindi, perché l'implementazione funzioni correttamente, è imperativo che nel `rep` non compaiano duplicati (altrimenti la rimozione non rimuoverebbe tutti gli elementi uguali ad `x`). Dunque, ad esempio, anche `[1, 1, 2]` è uno stato concreto inammissibile.

