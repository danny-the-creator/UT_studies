import java.sql.*;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;
import java.io.*;
public class IsolationBreach {
    public static Connection conn;
    static Scanner sc = new Scanner(System.in);
    static String dbuser = "dab_di23242b_100"; // TODO: CHANGE THIS LINE
    static String passwd = "TezErvXbIwVFv/sY"; // TODO: CHANGE THIS LINE
    public static void main (String[] args) {
        try {
            Class.forName("org.postgresql.Driver");
            try {
                conn = DriverManager.getConnection(
                        "jdbc:postgresql://bronto.ewi.utwente.nl/"+dbuser,
                        dbuser, passwd);
                conn.setAutoCommit(true);
                conn.setTransactionIsolation(Connection.TRANSACTION_NONE);
                // Preliminaries
                System.out.println("Isolation Breach test");
                System.out.println();
                BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));
                String str = reader.readLine();
                double chg = Double.parseDouble(str);
                System.out.println("Amount to be transferred : "+chg);
                System.out.println();
                System.out.println("Initialize accounts");
                updateAccount("A",1000);
                updateAccount("B",2000);
                System.out.println();
                // Now start the scenario
                transferMoney(chg);
                // Finalize
                conn.setAutoCommit(true);
                conn.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
                System.out.println();
                System.out.println("Final state in database");
                readAccount("A");
                readAccount("B");
                conn.close();
            } catch(SQLException e) {
                System.err.println("Oops: " + e.getMessage() );
                System.err.println("SQLState: " + e.getSQLState() );
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
        catch (ClassNotFoundException e) {
            System.err.println("JDBC driver not loaded");
        }
    }
    public static void waitForKey(String msg) {
        System.out.print(msg+" ... Press ENTER");
        sc.nextLine();
        // Reads everything until the ENTER
        // We do not use System.in.read() because on Windows a
        // return/enter produces TWO characters
    }
    public static void transferMoney(double chg) {
        waitForKey("a:=read A");
        double a=readAccount("A");
        System.out.println();
        waitForKey("b:=read B");
        double b=readAccount("B");
        System.out.println();
        waitForKey("put "+(a-chg)+" in A");
        updateAccount("A",a-chg);
        System.out.println();
        waitForKey("put "+(b+chg)+" in B");
        updateAccount("B",b+chg);
    }
    public static double readAccount(String acc) {
        double amount=0;
        String query="SELECT amount From account WHERE name='"+acc+"'";
        try {
            Statement st = conn.createStatement();
            System.out.println("Query: "+query);
            ResultSet rs = st.executeQuery(query);
            while (rs.next())
            {
                amount=rs.getDouble("amount");
                System.out.println("Result for account "+acc+" : "+amount);
            }
            rs.close();
            st.close();
        } catch(SQLException e) {
            System.err.println("Oops: " + e.getMessage() );
            System.err.println("SQLState: " + e.getSQLState() );
        }
        return amount;
    }
    public static void updateAccount(String acc, double amount) {
        String query="UPDATE account SET amount="+amount+"WHERE name='"+acc+"'";
        try {
            Statement st = conn.createStatement();
            System.out.println("Query: "+query);
            st.executeUpdate(query);
            System.out.println("Done");
            st.close();
        } catch(SQLException e) {
            System.err.println("Oops: " + e.getMessage() );
            System.err.println("SQLState: " + e.getSQLState() );
        }
    }
}