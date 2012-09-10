package queue;

public class QueueNode {
	public Boolean data;
	public QueueNode next;
	
	public QueueNode(Boolean data, QueueNode next) {
		this.data = data;
		this.next = next;
	}
}
