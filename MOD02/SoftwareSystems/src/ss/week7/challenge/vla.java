package ss.week7.challenge;

import java.util.HashMap;
import java.util.Set;

public interface vla {
    HashMap<String,Integer> scores = new HashMap<>();
    HashMap<String,Integer> counts = new HashMap<>();
    //@ ensures getScore(name) == \old(getScore(name))+4;
    //@ ensures getCount(name) == \old(getCount(name))+1;
    //@ ensures getProgrammers().contains(name);
    //@ ensures (\forall String i; getProgrammers().contains(i); getScore(i) == \old(getScore(i)) || name.equals(i));
    //@ensures (\forall String i; getProgrammers().contains(i); getCount(i) == \old(getCount(i)) || name.equals(i));
    public void good(String name);
    //@ ensures getScore(name) == \old(getScore(name))/2;
    //@ ensures getCount(name) == \old(getCount(name))+1;
    //@ ensures getProgrammers().contains(name);
    //@ ensures (\forall String i; getProgrammers().contains(i); getScore(i) == \old(getScore(i)) || name.equals(i));
    //@ensures (\forall String i; getProgrammers().contains(i); getCount(i) == \old(getCount(i)) || name.equals(i));
    public void bad(String name);
    //@ ensures getScore(name)== \old(getScore(name))-7;
    //@ ensures getCount(name) == \old(getCount(name))+1;
    //@ ensures getProgrammers().contains(name);
    //@ ensures (\forall String i; getProgrammers().contains(i); getScore(i) == \old(getScore(i)) || name.equals(i));
    //@ensures (\forall String i; getProgrammers().contains(i); getCount(i) == \old(getCount(i)) || name.equals(i));
    public void ugly(String name);




    //@ ensures (getCount(name) == 0) ==> \result==0;
    //@ ensures (getCount(name)!=0) ==> \result == scores.get(name);
    public int getScore(String name) throws ProgrammerNotFound;
    //@ ensures (getCount(name) == 0) ==> \result==0;
    //@ ensures (getCount(name)!=0) ==> \result == counts.get(name);
    public int getCount(String name) throws ProgrammerNotFound;
    //@ ensures \result == counts.keySet();
    public Set<String> getProgrammers();
}
