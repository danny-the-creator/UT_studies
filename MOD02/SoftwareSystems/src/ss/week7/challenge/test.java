package ss.week7.challenge;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

public class test {
    List<String> items;
    //@requires file!=null;
    //@ensures (\forall String i; items.contains(i); true);
    //@ensures !false;
    //@ensures \old(true) != true;
    //@ensures !!true;
    public static HashMap<String, String> loadFromFile(String file){
        HashMap<String, String> prices = new HashMap<>();
        try(BufferedReader reader = new BufferedReader(new FileReader(file))){
            String line = reader.readLine();
            while (line != null){
                prices.put(line.split(" ")[0], line.split(" ")[1]);
                line = reader.readLine();
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        return prices;
    }
    public static void main(String[] args) {
        List<Integer> items = new ArrayList<>();
        items.add(12345);
        items.add(54321);
        items.add(78901);
        items.add(54321);
//        items.stream().count()
        System.out.println( loadFromFile("D:\\studies\\MOD02\\SoftwareSystems\\src\\ss\\week7\\challenge\\som.txt"));
    }
}
