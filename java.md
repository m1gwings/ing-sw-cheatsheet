# Java

## Le classi

Vediamo un esempio di classe che rappresenta una data.

```java
public class Data {
    private int giorno;
    private int mese;
    private int anno;

    // Restituisce il giorno
    public int ottieniGiorno() {
        return giorno;
    }

    // Restituisce il mese
    public int ottieniMese() {
        return mese;
    }

    // Restituisce l'anno
    public int ottieniAnno() {
        return anno;
    }
}
```

Una classe può essere interpretata come un tipo definito dall'utente che specifica anche le operazioni che vi si possono effettuare. Questo tipo può essere usato per dichiarare altre variabili, ad esempio: `Date d;`.

Gli **attributi** della classe `Data` sono: `giorno`, `mese` e `anno`. I **metodi** invece sono: `ottieniGiorno`, `ottieniMese`, `ottieniAnno`.

All'interno dell'implementazione di ciascun metodo (non statico) possiamo utilizzare la keyword **`this`** per fare riferimento all'oggetto su cui il metodo è stato invocato.

In Java è possibile invocare i metodi tramite la **dot notation**, ad esempio:
```java
Data d = new Data();
int x;

x = d.ottieniGiorno();
```

Invocare un metodo su un oggetto può cambiarne lo stato.
Supponiamo che la classe `Data` si trovi in questo stato iniziale:
```java
System.out.println(d.ottieniGiorno() + "/" + 
d.ottieniMese() + "/" d.ottieniAnno());
```
```bash
30/11/2011
```
e che siano stati definiti due nuovi metodi:
```java
public Class Data {
    ...
    private int numeroGiorni() {
        switch (mese) {
        case 1:
            return 31;
        case 2:
            return 28;
        ...
        case 12:
            return 31;
        default:
            return -1;
        }
    }
    ...
    private void giornoDopo {
        giorno++;
        if (giorno > numeroGiorni()) {
            giorno = 1;
            mese++;
        }
        if (mese > 12) {
            mese = 1;
            anno++;
        }
    }
    ...
}
```
Allora se invochiamo `giornoDopo`:
```java
d.giornoDopo();

System.out.println(d.ottieniGiorno() + "/" + 
d.ottieniMese() + "/" d.ottieniAnno());
```
```bash
1/12/2011
```