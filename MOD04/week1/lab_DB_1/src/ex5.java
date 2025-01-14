import java.sql.*;
public class ex5 {
    public static void main(String[] args) {
        try {
            Class.forName("org.postgresql.Driver");
        } catch (ClassNotFoundException e) {
            System.out.println("Error loading driver: "+e);
        }
        String host = "bronto.ewi.utwente.nl";
        String dbName = "?currentSchema=movies";
        String url = "jdbc:postgresql://"
                + host + ":5432/" + dbName;
        try {
            Connection connection =
                    DriverManager.getConnection(url, "dab_di23242b_100", "TezErvXbIwVFv/sY");
            Statement statement = connection.createStatement();
        }
        catch(SQLException sqle) {
            System.err.println("Error connecting: " + sqle);
        }

    }
}
