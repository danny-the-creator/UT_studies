package ss.week6.dictionaryattack;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.HashMap;
import java.util.Map;
import org.apache.commons.codec.binary.Hex;


public class DictionaryAttack {
    private Map<String, String> passwordMap =new HashMap<>() ;
    private Map<String, String> hashDictionary =new HashMap<>();

    /**
     * Reads a password file. Each line of the password file has the form:
     * username: encodedpassword
     * After calling this method, the passwordMap class variable should be
     * filled with the content of the file. The key for the map should be
     * the username, and the password hash should be the content.
     * @param filename
     * @throws IOException
     */
    public void readPasswords(String filename) throws IOException{
        BufferedReader reader = new BufferedReader(new FileReader(filename));
        String line;
        while ((line = reader.readLine())!= null){
            passwordMap.put(line.split(": ")[0],line.split(": ")[1]);
//			System.out.println(line.split(": ")[0]+line.split(": ")[1]);
        }
		reader.close();
    }

    /**
     * Given a password, return the MD5 hash of a password. The resulting
     * hash (or sometimes called digest) should be hex-encoded in a String.
     * @param password
     * @return
     */
    public String getPasswordHash(String password) {
        byte[] inputData = password.getBytes();
        MessageDigest md = null;
        try {
            md = MessageDigest.getInstance("MD5");
        } catch (NoSuchAlgorithmException e) {
            throw new RuntimeException(e);
        }
        md.update(inputData);
        return Hex.encodeHexString(md.digest());
    }

    /**
     * Checks the password for the user the password list. If the user
     * does not exist, returns false.
     * @param user
     * @param password
     * @return whether the password for that user was correct.
     */
    public boolean checkPassword(String user, String password) {
        String hashPass = passwordMap.get(user);
        if (hashPass == null) {
            return false;
        }
        return getPasswordHash(password).equals(hashPass);
    }

    /**
     * Reads a dictionary from file (one line per word) and use it to add
     * entries to a dictionary that maps password hashes (hex-encoded) to
     * the original password.
     * @param filename filename of the dictionary.
     */
    public void addToHashDictionary(String filename) throws IOException {
        BufferedReader reader = new BufferedReader(new FileReader(filename));
        String line;
        while ((line = reader.readLine()) != null) {
            hashDictionary.put(getPasswordHash(line), line);
        }
        reader.close();
    }

    /**
     * Do the dictionary attack.
     */
    public void doDictionaryAttack () throws IOException {
		addToHashDictionary("D:\\studies\\MOD02\\SoftwareSystems\\test\\ss\\week6\\pass");
		readPasswords("D:\\studies\\MOD02\\SoftwareSystems\\test\\ss\\week6\\LeakedPasswords.txt");
        String value;
        for (String key : passwordMap.keySet()) {
            value = passwordMap.get(key);
            if (hashDictionary.containsKey(value)) {
                System.out.println(key + ": " + hashDictionary.get(value));
            }
        }
    }

    public static void main(String[] args) throws IOException {
        DictionaryAttack da = new DictionaryAttack();
        // To implement
        da.doDictionaryAttack();
    }

}
