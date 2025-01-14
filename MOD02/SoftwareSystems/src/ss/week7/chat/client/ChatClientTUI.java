package ss.week7.chat.client;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.util.Objects;
import java.util.Scanner;
import ss.week7.chat.protocol.Protocol;
import ss.week7.chat.server.ChatServer;

public class ChatClientTUI implements ClientListener {
    public static void main(String[] args) throws IOException {
        ChatClientTUI chatClientTUI = new ChatClientTUI();
        chatClientTUI.runTUI();
    }

    private void runTUI() throws IOException {
        String message;
        BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
        System.out.println("Enter port:");
        int port = Integer.parseInt(in.readLine());
        System.out.println("Enter address:");
        String ser = in.readLine();

        ChatClient chatClient = new ChatClient(ser, port);
        System.out.println("Enter username: ");
        String username = in.readLine();
        chatClient.sendUsername(username);

        chatClient.addListener(new LogListener("D:\\studies\\MOD02\\SoftwareSystems\\src\\ss\\week7\\chat\\client\\ChatHistory.txt"));

        chatClient.addListener(this);
        chatClient.start();
        while (true){
            System.out.println("Enter the message: ");
            message = in.readLine();
            if (Objects.equals(message, "quit")){
                chatClient.removeListener(this);
                chatClient.close();
                break;
            }
            chatClient.sendChatMessage(message);
        }
    }

    @Override
    public void chatMessage(String name, String message) {
        System.out.println(Protocol.FROM+Protocol.SEPARATOR+name+Protocol.SEPARATOR+message);
    }

    @Override
    public void connectionLost() {
        System.out.println("Connection Lost");
        System.exit(0);

    }
}