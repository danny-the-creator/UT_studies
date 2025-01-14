package ss.week7.challenge;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class CodeScoresImpl implements vla {
    private final Map<String, Integer> scores = new HashMap<>();
    private final Map<String, Integer> counts = new HashMap<>();
    private final String friend = "Bob";
    @Override
    public synchronized void good(String name) {
        try {
            scores.put(name, getScore(name) + 4);
            counts.put(name, getCount(name) + 1);
        } catch (ProgrammerNotFound e) {
            throw new RuntimeException(e);
        }

    }
    @Override
    public synchronized void bad(String name) {
        try {
            scores.put(name, getScore(name) / 2);
            counts.put(name, getCount(name) + 1);
        } catch (ProgrammerNotFound e) {
            throw new RuntimeException(e);
        }

    }
    @Override
    public synchronized void ugly(String name) {
        try {
            scores.put(name, getScore(name) - 7);
            counts.put(name, getCount(name) + 1);
            notifyAll();
        } catch (ProgrammerNotFound e) {
            throw new RuntimeException(e);
        }

    }
    @Override
    public int getScore(String name) throws ProgrammerNotFound {
        if (!getProgrammers().contains(name)){
            throw new ProgrammerNotFound(name);
        }
        return scores.getOrDefault(name, 0);
    }
    @Override
    public int getCount(String name) throws ProgrammerNotFound {
        if (!getProgrammers().contains(name)){
            throw new ProgrammerNotFound(name);
        }
        return counts.getOrDefault(name, 0);
    }
    @Override
    public Set<String> getProgrammers() {
        return new HashSet<>(scores.keySet());
    }
    //@ ensures \result != null ==>((\forall String name; getProgrammers().contains(name) ; getScore(\result) <= getScore(name) ));
    //@ ensures \result == null ==>(\forall int score; scores.values().contains(score); score == 0);
    public String getWorstProgrammers(){
        String worst = null;
        int worstScore = Integer.MAX_VALUE;
        for (String name : counts.keySet()){
            if (counts.get(name)!=0 && !name.equals(friend)){
                if (scores.get(name)< worstScore){
                    worst=name;
                    worstScore = scores.get(name);
                }
            }
        }
        return worst;
    }
    public String waitForNegative(){
        while (true){
            try {
                wait();
            } catch (InterruptedException e) {
                System.out.println(e);
            }
            for (String name: getProgrammers()){
                if (scores.get(name)<0){
                    return name;
                }
            }
        }
    }
}