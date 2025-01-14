package ss.week7.chat.client;

import java.io.*;

public class LogListener implements ClientListener{
    BufferedWriter writer;
    public LogListener(String  file){
        try {
            writer = new BufferedWriter(new FileWriter(file));
//            System.out.println("you");
        } catch (IOException e) {
            throw new RuntimeException(e);
        }

    }

    @Override
    public void chatMessage(String name, String message) {
        //        System.out.println("hi0");

        try {
            //                System.out.println("hi1");
            writer.write("<"+name+">"+" said: "+"\"<"+message+">\"\n");
            writer.flush();
            //                System.out.println("hi2");
        } catch (IOException e) {
            //                System.out.println("hi2.5");
            throw new RuntimeException(e);
        }

    }

    @Override
    public void connectionLost() {
        try {
            try {
                writer.write("Connection Lost!");
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        } finally {
            try {
                writer.close();
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }

    }
}
